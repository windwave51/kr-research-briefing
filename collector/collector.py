#!/usr/bin/env python3
"""국내 연구기관 간행물 수집기 (1차). 모델 API 없이 표준 라이브러리로 돈다. PDF 본문 추출에만 pypdf가 필요하다.

명령: sources, probe, collect, status, pending, search, inspect, evidence, attach, export-new
collect --meta-only는 원문(첨부·상세 페이지)을 저장하지 않고 제목·발간일·원문 링크만 남긴다(GitHub 동향 갱신용).
수집 범위는 각 게시판 첫 화면의 최신 목록이다. 기관 전체를 모았다는 뜻이 아니다.
날짜를 재현하려면 --as-of YYYY-MM-DD를 준다.
"""
import argparse
import collections
import datetime as dt
import hashlib
import html
from html.parser import HTMLParser
import io
import json
import logging
from pathlib import Path
import re
import sqlite3
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parent
TOKEN = "DomesticResearchPilot"
AGENT = "Mozilla/5.0 (compatible; DomesticResearchPilot/0.1)"
MAX_BYTES = 40 * 1024 * 1024
VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"}
# form은 일부러 넣지 않는다. 국내 공공기관 사이트는 본문 전체를 form으로 감싸는 경우가 있다.
IGNORE = {"script", "style", "noscript", "svg", "template"}
DATE_RE = re.compile(r"(?<!\d)(\d{4})\s*(?:[.\-/]|년)\s*(\d{1,2})\s*(?:[.\-/]|월)\s*(\d{1,2})(?!\d)")
WAF_PHRASES = ("contrary to the web firewall security policies", "웹 방화벽", "비정상적인 접근")
LOGIN_PHRASES = ("로그인이 필요", "로그인 후 이용", "회원만 이용", "회원 전용", "권한이 없습니다")
REVIEW_STATES = ("in_window", "undated_review", "date_conflict_review")


class CollectionError(Exception):
    pass


class Blocked(CollectionError):
    """웹방화벽 등으로 차단됨. 같은 기관에 더 요청하지 않는다."""


# ---------------------------------------------------------------- 문자열·날짜·주소

def clean(value):
    return re.sub(r"\s+", " ", html.unescape(str(value or ""))).strip()


def find_date(text, label=None):
    """첫 번째 유효한 연-월-일을 찾는다. 연도만 있거나 월까지만 있으면 날짜를 지어내지 않고 None을 돌려준다."""
    text = clean(text)
    raw = None
    if label:
        i = text.find(label)
        if i < 0:
            return None, None
        text = text[i + len(label):i + len(label) + 40]
        raw = text.strip()[:20]
    for m in DATE_RE.finditer(text):
        try:
            return dt.date(*map(int, m.groups())).isoformat(), m.group(0)
        except ValueError:
            continue
    return None, raw


def canonical(url, keep=None):
    p = urllib.parse.urlsplit(html.unescape(str(url)).strip())
    if p.scheme not in ("http", "https") or p.username or p.password or not p.hostname:
        raise ValueError("Only public HTTP(S) URLs are supported")
    path = re.sub(r";jsessionid=[^/?#]*", "", p.path or "/", flags=re.I)
    query = urllib.parse.parse_qsl(p.query, keep_blank_values=True)
    if keep is not None:
        values = dict(query)
        query = [(k, values[k]) for k in keep if values.get(k)]
    else:
        query = [(k, v) for k, v in query
                 if not k.lower().startswith("utm_") and k.lower() not in {"fbclid", "gclid", "trk"}]
    return urllib.parse.urlunsplit((p.scheme.lower(), p.netloc.lower(), path, urllib.parse.urlencode(query), ""))


def allowed(institution, url):
    p = urllib.parse.urlsplit(url)
    host = (p.hostname or "").lower()
    return p.scheme in ("http", "https") and not p.username and not p.password and any(
        host == d or host.endswith("." + d) for d in institution["domains"])


def local_part(url):
    p = urllib.parse.urlsplit(url)
    return p.path + ("?" + p.query if p.query else "")


# ---------------------------------------------------------------- robots.txt (RFC 9309)

class Robots:
    """RFC 9309 방식으로 읽는다. 가장 긴 규칙이 이기고, 길이가 같으면 Allow가 이긴다.
    형식이 깨진 Disallow 값은 안전하게 Disallow: / 로 본다."""

    def __init__(self, text):
        self.groups = []
        agents, rules, in_rules = [], [], False
        for raw in (text or "").splitlines():
            line = raw.split("#", 1)[0].strip()
            if ":" not in line:
                continue
            key, value = line.split(":", 1)
            key, value = key.strip().lower(), value.strip()
            if key == "user-agent":
                if in_rules:
                    self.groups.append((agents, rules))
                    agents, rules, in_rules = [], [], False
                agents.append(value.lower())
            elif key in ("allow", "disallow"):
                in_rules = True
                if not agents or (key == "disallow" and value == ""):
                    continue
                if not value.startswith(("/", "*")):
                    if key == "allow":
                        continue
                    value = "/"
                rules.append((key == "allow", value))
            elif key == "crawl-delay":
                in_rules = True
        if agents:
            self.groups.append((agents, rules))

    def rules_for(self, token):
        token = token.lower()

        def names_us(agents):
            return any(a not in ("", "*") and a in token for a in agents)

        if any(names_us(agents) for agents, _ in self.groups):
            return [r for agents, rules in self.groups if names_us(agents) for r in rules]
        return [r for agents, rules in self.groups for r in rules if "*" in agents]

    def allows(self, token, url):
        path = local_part(url)
        if path == "/robots.txt":
            return True
        best = None
        for allow, pattern in self.rules_for(token):
            regex = "^" + re.escape(pattern).replace(r"\*", ".*")
            if regex.endswith(r"\$"):
                regex = regex[:-2] + "$"
            if re.match(regex, path):
                rank = (len(pattern), allow)
                if best is None or rank > best:
                    best = rank
        return True if best is None else best[1]


# ---------------------------------------------------------------- HTML

class Node:
    def __init__(self, tag="root", attrs=(), parent=None):
        self.tag, self.attrs, self.parent, self.children = tag, dict(attrs), parent, []

    def walk(self):
        yield self
        for child in self.children:
            if isinstance(child, Node):
                yield from child.walk()

    def text(self):
        if self.tag in IGNORE or "hidden" in self.attrs or self.attrs.get("aria-hidden") == "true":
            return ""
        return clean(" ".join(c.text() if isinstance(c, Node) else c for c in self.children))

    def classes(self):
        return (self.attrs.get("class") or "").split()


class DocumentParser(HTMLParser):
    def __init__(self, data):
        super().__init__(convert_charrefs=True)
        self.root = self.current = Node()
        self.feed(data)

    def handle_starttag(self, tag, attrs):
        n = Node(tag, attrs, self.current)
        self.current.children.append(n)
        if tag not in VOID:
            self.current = n

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        n = self.current
        while n.parent:
            if n.tag == tag:
                self.current = n.parent
                return
            n = n.parent

    def handle_data(self, data):
        self.current.children.append(data)

    def nodes(self, tag):
        return [n for n in self.root.walk() if n.tag == tag]

    def by_class(self, name):
        return next((n for n in self.root.walk() if name in n.classes()), None)

    def og_title(self):
        for n in self.nodes("meta"):
            if n.attrs.get("property") == "og:title" and n.attrs.get("content"):
                return clean(n.attrs["content"]).split(" - ")[0].strip()
        titles = self.nodes("title")
        return titles[0].text().split(" - ")[0].strip() if titles else ""


def target_of(node):
    href = (node.attrs.get("href") or "").strip()
    if href and not href.lower().startswith("javascript") and not href.startswith("#"):
        return href
    m = re.search(r"location\.href\s*=\s*['\"]([^'\"]+)['\"]", node.attrs.get("onclick") or "")
    return m.group(1) if m else None


def container_of(node):
    n = node.parent
    while n is not None and n.tag not in ("li", "tr"):
        n = n.parent
    return n or node.parent or node


def link_attributes(node):
    return " ".join(v for n in node.walk() for k, v in n.attrs.items() if k in ("href", "onclick") and v)


def absolute(base, url):
    return canonical(urllib.parse.urljoin(base, html.unescape(url)))


def discover(publication, text, final):
    """게시판 목록에서 항목을 뽑는다. 최신순(sort_key 내림차순)으로 돌려준다."""
    spec = publication["list"]
    parser = DocumentParser(text)
    items = []
    if spec["mode"] == "options":
        for select in parser.nodes("select"):
            if spec["onchange"] in (select.attrs.get("onchange") or ""):
                for option in (n for n in select.walk() if n.tag == "option"):
                    value = (option.attrs.get("value") or "").strip()
                    if value.isdigit():
                        items.append(dict(url=canonical(spec["template"].format(value)), title=option.text(),
                                          published=None, published_raw=None, attachment_url=None,
                                          attachment_resolve=None))
                break
    else:
        pattern = re.compile(spec["item"])
        for node in parser.root.walk():
            if node.tag not in ("a", "button"):
                continue
            target = target_of(node)
            if not target:
                continue
            try:
                url = canonical(urllib.parse.urljoin(final, target), spec.get("keep"))
            except ValueError:
                continue
            if not pattern.search(local_part(url)):
                continue
            box = container_of(node)
            title_node = next((n for n in node.walk() if n.tag == spec["title_tag"]), None) if spec.get("title_tag") else None
            published, raw = find_date(box.text(), spec.get("date_label"))
            attachment, resolve = None, None
            rules = spec.get("attachment") or []
            for rule in (rules if isinstance(rules, list) else [rules]):
                m = re.search(rule["pattern"], link_attributes(box))
                if m:
                    attachment = absolute(final, rule.get("template", "{0}").format(m.group(1)))
                    resolve = rule.get("resolve")
                    break
            items.append(dict(url=url, title=(title_node or node).text(), published=published,
                              published_raw=raw, attachment_url=attachment, attachment_resolve=resolve))
    merged = collections.OrderedDict()
    for item in items:
        old = merged.get(item["url"])
        if old is None:
            merged[item["url"]] = item
            continue
        for key, value in item.items():
            if value and (not old.get(key) or (key == "title" and len(value) > len(old[key]))):
                old[key] = value
    result = list(merged.values())
    if spec.get("sort_key"):
        def key(item):
            m = re.search(spec["sort_key"], item["url"])
            return int(m.group(1)) if m else -1
        result.sort(key=key, reverse=True)
    return result


def read_detail(publication, text, final):
    spec = publication.get("detail") or {}
    parser = DocumentParser(text)
    out = {}
    if spec.get("title") == "og":
        out["title"] = parser.og_title()
    if spec.get("date_after"):
        i = text.find(spec["date_after"])
        if i >= 0:
            out["published"], out["published_raw"] = find_date(re.sub(r"<[^>]+>", " ", text[i:i + 20000]))
    attachment = spec.get("attachment")
    if attachment:
        start = max(text.find(attachment["after"]), 0) if attachment.get("after") else 0
        m = re.search(attachment["pattern"], text[start:])
        if m:
            out["attachment_url"] = absolute(final, attachment.get("template", "{0}").format(html.unescape(m.group(1))))
    node = parser.by_class(spec["body_class"]) if spec.get("body_class") else None
    if node is None:
        node = next(iter(parser.nodes("main") + parser.nodes("article")), None)
    body = node.text() if node is not None else ""
    out["text"] = body
    out["body_status"] = "html_extracted_unverified" if len(body) > 500 else "html_preview"
    lowered = (out.get("title", "") + " " + body[:2000]).lower()
    if any(p in lowered for p in LOGIN_PHRASES):
        out["body_status"] = "restricted_login"
    return out


# ---------------------------------------------------------------- 내려받기

Response = collections.namedtuple("Response", "data mime final charset disposition")


def decode(data, charset=None):
    candidates = [charset] if charset else []
    meta = re.search(rb"<meta[^>]+charset=[\"']?([\w-]+)", data[:4096], re.I)
    if meta:
        candidates.append(meta.group(1).decode("ascii", "ignore"))
    candidates += ["utf-8", "cp949"]
    for name in candidates:
        try:
            return data.decode(name)
        except (LookupError, UnicodeDecodeError):
            continue
    return data.decode("utf-8", errors="replace")


def sniff(data):
    if data.startswith(b"%PDF-"):
        return "pdf"
    if data.startswith(b"\xd0\xcf\x11\xe0"):
        return "ole"  # HWP 5.x, 구형 MS Office
    if data.startswith(b"PK\x03\x04"):
        return "zip"  # HWPX, DOCX 등
    head = data[:512].lstrip().lower()
    if head.startswith((b"<!doctype", b"<html", b"<?xml", b"<")):
        return "html"
    return "unknown"


def attachment_name(disposition):
    if not disposition:
        return None
    m = re.search(r"filename\*\s*=\s*(?:UTF-8|utf-8)''([^;]+)", disposition)
    if m:
        return urllib.parse.unquote(m.group(1).strip().strip('"'))
    m = re.search(r"filename\s*=\s*\"?([^\";]+)\"?", disposition, re.I)
    if not m:
        return None
    raw = m.group(1).strip()
    try:
        data = raw.encode("latin-1")
    except UnicodeEncodeError:
        return urllib.parse.unquote(raw)
    for name in ("utf-8", "cp949"):
        try:
            return urllib.parse.unquote(data.decode(name))
        except UnicodeDecodeError:
            continue
    return raw


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def __init__(self, institution):
        self.institution = institution

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if not allowed(self.institution, newurl):
            raise CollectionError("redirect_outside_official_domains: " + newurl)
        return super().redirect_request(req, fp, code, msg, headers, newurl)


class Client:
    def __init__(self, timeout=25, delay=1.0):
        self.timeout, self.delay, self.robots, self.last = timeout, delay, {}, {}

    def _open(self, institution, url, referer=None, limit=MAX_BYTES):
        if not allowed(institution, url):
            raise CollectionError("outside_official_domains: " + url)
        host = urllib.parse.urlsplit(url).netloc
        wait = self.last.get(host, 0) + self.delay - time.monotonic()
        if wait > 0:
            time.sleep(wait)
        headers = {"User-Agent": AGENT, "Accept-Language": "ko-KR,ko;q=0.9,en;q=0.5",
                   "Accept": "text/html,application/pdf;q=0.9,*/*;q=0.5"}
        if referer:
            headers["Referer"] = referer
        try:
            request = urllib.request.Request(url, headers=headers)
            with urllib.request.build_opener(SafeRedirect(institution)).open(request, timeout=self.timeout) as r:
                data = r.read(limit + 1)
                if len(data) > limit:
                    raise CollectionError("response_too_large")
                return Response(data, r.headers.get_content_type(), r.geturl(), r.headers.get_content_charset(),
                                r.headers.get("Content-Disposition"))
        finally:
            self.last[host] = time.monotonic()

    def policy(self, institution, url):
        if institution.get("robots_override") == "disallow_all":
            raise CollectionError("robots_disallowed_override")
        p = urllib.parse.urlsplit(url)
        origin = p.scheme + "://" + p.netloc
        if origin not in self.robots:
            try:
                r = self._open(institution, origin + "/robots.txt", limit=1024 * 1024)
                self.robots[origin] = Robots(decode(r.data, r.charset))
            except urllib.error.HTTPError as e:
                if e.code in (404, 410):
                    self.robots[origin] = Robots("")
                elif e.code in (401, 403):
                    raise CollectionError("robots_access_denied")
                else:
                    raise CollectionError("robots_unavailable_http_%d" % e.code)
        return self.robots[origin]

    def get(self, institution, url, referer=None):
        if not self.policy(institution, url).allows(TOKEN, url):
            raise CollectionError("robots_disallowed: " + local_part(url))
        r = self._open(institution, url, referer)
        if r.final != url and not self.policy(institution, r.final).allows(TOKEN, r.final):
            raise CollectionError("robots_disallowed_redirect: " + local_part(r.final))
        if sniff(r.data) == "html":
            head = decode(r.data[:6000], r.charset).lower()
            if any(p in head for p in WAF_PHRASES):
                raise Blocked("blocked_by_waf: " + local_part(url))
        return r


def file_host(institution, url):
    """기관이 파일을 외부 저장소에 두는 경우, sources.json의 file_hosts에 적힌 호스트·경로만 허용한다."""
    p = urllib.parse.urlsplit(url)
    for rule in institution.get("file_hosts", []):
        if p.scheme == "https" and p.hostname == rule["host"] and p.path.startswith(rule["path_prefix"]):
            return {"name": institution["name"] + " 파일 저장소", "domains": [rule["host"]]}
    raise CollectionError("attachment_host_not_permitted: " + (p.hostname or url))


def fetch_attachment(client, institution, item, url):
    if item.get("attachment_resolve") == "url_text":
        # 버튼이 먼저 파일 주소를 문자열로 받아 온 뒤 그 주소로 이동하는 방식 (KINU fileDown2)
        r = client.get(institution, url, referer=item["url"])
        target = urllib.parse.unquote(decode(r.data, r.charset).strip())
        return client.get(file_host(institution, target), target, referer=item["url"])
    return client.get(institution, url, referer=item["url"])


# ---------------------------------------------------------------- PDF

def extract_pdf(data):
    try:
        from pypdf import PdfReader
    except ImportError:
        return "", "pdf_parser_missing", None, []
    # 글꼴 경고(fontTools 등)는 본문 추출 결과에 영향이 없을 때가 많아 출력을 어지럽히지 않게 숨긴다.
    logging.getLogger("pypdf").setLevel(logging.ERROR)
    reader = PdfReader(io.BytesIO(data))
    pages = []
    for i, page in enumerate(reader.pages):
        try:
            text = page.extract_text() or ""
        except Exception:
            text = ""
        pages.append("[PAGE %d]\n%s" % (i + 1, text))
    body = "\n\n".join(pages)
    letters = len(re.findall(r"[가-힣A-Za-z]", body))
    odd = len(re.findall(r"[�-]", body))
    flags = ["pdf_text_garbled"] if body and odd > 0.05 * max(len(body), 1) else []
    status = "pdf_extracted_unverified" if letters > 300 else "pdf_needs_ocr"
    return body, status, len(pages), flags


def bigrams(value):
    s = re.sub(r"[^0-9a-z가-힣]", "", value.lower())
    return {s[i:i + 2] for i in range(len(s) - 1)}


def title_matches(title, text):
    """원문 앞부분에 제목의 글자쌍이 60% 이상 있으면 같은 문서로 본다. 판단할 수 없으면 None."""
    wanted = bigrams(re.sub(r"\[[^\]]*\]|\([^)]*\)", " ", title or ""))
    if len(wanted) < 3:
        return None
    head = text.split("[PAGE 5]", 1)[0][:20000]
    return len(wanted & bigrams(head)) / len(wanted) >= 0.6


# ---------------------------------------------------------------- 저장

def load_sources():
    config = json.loads((ROOT / "sources.json").read_text(encoding="utf-8"))
    return config["institutions"], config["publications"]


def connect(data_dir):
    data_dir.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(str(data_dir / "research.sqlite3"))
    db.row_factory = sqlite3.Row
    db.executescript("""
      PRAGMA foreign_keys=ON;
      CREATE TABLE IF NOT EXISTS publications(id TEXT PRIMARY KEY, config TEXT NOT NULL);
      CREATE TABLE IF NOT EXISTS checks(id INTEGER PRIMARY KEY, publication_id TEXT, checked_at TEXT, status TEXT,
        discovered INTEGER DEFAULT 0, new INTEGER DEFAULT 0, detail TEXT);
      CREATE TABLE IF NOT EXISTS documents(id TEXT PRIMARY KEY, publication_id TEXT, institution TEXT, url TEXT UNIQUE,
        title TEXT, published TEXT, published_raw TEXT, first_seen TEXT, last_seen TEXT, date_status TEXT,
        body_status TEXT, current_version INTEGER, attachment_url TEXT, attachment_status TEXT,
        attachment_name TEXT, quality_flags TEXT DEFAULT '[]');
      CREATE TABLE IF NOT EXISTS versions(id INTEGER PRIMARY KEY, document_id TEXT REFERENCES documents(id),
        retrieved_at TEXT, fingerprint TEXT, representation TEXT, text TEXT, raw_path TEXT, mime TEXT,
        page_count INTEGER, UNIQUE(document_id, fingerprint));
      CREATE TABLE IF NOT EXISTS document_checks(id INTEGER PRIMARY KEY, publication_id TEXT, url TEXT,
        checked_at TEXT, status TEXT, detail TEXT);
      CREATE TABLE IF NOT EXISTS evidence(id INTEGER PRIMARY KEY, document_id TEXT REFERENCES documents(id),
        version_id INTEGER REFERENCES versions(id), kind TEXT, claim TEXT, quote TEXT, page INTEGER,
        created_at TEXT);
    """)
    for p in load_sources()[1]:
        db.execute("INSERT OR REPLACE INTO publications VALUES (?,?)", (p["id"], json.dumps(p, ensure_ascii=False)))
    db.commit()
    return db


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")


def save_raw(data_dir, data):
    kind = sniff(data)
    extension = {"pdf": "pdf", "html": "html", "ole": "hwp", "zip": "zip"}.get(kind, "bin")
    path = data_dir / "raw" / (hashlib.sha256(data).hexdigest() + "." + extension)
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        path.write_bytes(data)
    return str(path.relative_to(data_dir))


def document_id(publication, url):
    return publication["institution"] + "-" + hashlib.sha256((publication["id"] + "|" + url).encode()).hexdigest()[:12]


def year_only(raw):
    m = re.match(r"\s*(\d{4})(?!\s*(?:[.\-/]|년)\s*\d)", raw or "")
    return int(m.group(1)) if m else None


def date_status(published, conflict, as_of, since, raw=None):
    if conflict:
        return "date_conflict_review"
    if not published:
        # 연도만 적힌 발행일(KINU 연례정세전망 등)은 날짜를 지어내지 않되, 확실히 지난 해의 것이면 창 밖으로 본다.
        year = year_only(raw)
        if year is not None and year < int(since[:4]):
            return "outside_window"
        return "undated_review"
    if published > as_of:
        return "future_quarantine"
    if published < since:
        return "outside_window"
    return "in_window"


def upsert_document(db, publication, doc):
    ident = document_id(publication, doc["url"])
    stamp = now()
    db.execute("""INSERT INTO documents(id,publication_id,institution,url,title,published,published_raw,first_seen,
        last_seen,date_status,body_status,attachment_url,attachment_status,attachment_name,quality_flags)
        VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT(id) DO UPDATE SET title=excluded.title,
        published=excluded.published,published_raw=excluded.published_raw,last_seen=excluded.last_seen,
        date_status=excluded.date_status,body_status=excluded.body_status,attachment_url=excluded.attachment_url,
        attachment_status=excluded.attachment_status,attachment_name=excluded.attachment_name,
        quality_flags=excluded.quality_flags""",
               (ident, publication["id"], publication["institution"], doc["url"], doc.get("title"), doc.get("published"),
                doc.get("published_raw"), stamp, stamp, doc["date_status"], doc.get("body_status"),
                doc.get("attachment_url"), doc.get("attachment_status"), doc.get("attachment_name"),
                json.dumps(sorted(set(doc.get("flags", []))))))
    return ident


def add_version(db, ident, representation, text, raw_path, mime, pages=None):
    fingerprint = hashlib.sha256((representation + "\n" + (text or "")).encode()).hexdigest()
    db.execute("""INSERT OR IGNORE INTO versions(document_id,retrieved_at,fingerprint,representation,text,raw_path,mime,
        page_count) VALUES(?,?,?,?,?,?,?,?)""", (ident, now(), fingerprint, representation, text, raw_path, mime, pages))
    version = db.execute("SELECT id FROM versions WHERE document_id=? AND fingerprint=?", (ident, fingerprint)).fetchone()[0]
    db.execute("UPDATE documents SET current_version=? WHERE id=?", (version, ident))
    return version


# ---------------------------------------------------------------- 수집

def selected(args):
    institutions, publications = load_sources()
    if not args.source:
        return institutions, publications
    wanted = set(args.source.split(","))
    unknown = wanted - {p["id"] for p in publications} - set(institutions)
    if unknown:
        raise ValueError("Unknown source IDs: " + ", ".join(sorted(unknown)))
    return institutions, [p for p in publications if p["id"] in wanted or p["institution"] in wanted]


def emit(**fields):
    print(json.dumps(fields, ensure_ascii=False))


def process(args, db, client, publication, institution, item):
    doc = dict(item, flags=[])
    detail = {}
    html_version = None
    if publication.get("detail"):
        r = client.get(institution, item["url"])
        if sniff(r.data) == "html":
            text = decode(r.data, r.charset)
            detail = read_detail(publication, text, r.final)
            if not args.meta_only:
                html_version = (detail["text"], save_raw(args.data, r.data), r.mime)
    if (publication.get("detail") or {}).get("title") == "og" and detail.get("title"):
        doc["title"] = detail["title"]
    elif not doc.get("title"):
        doc["title"] = detail.get("title")
    conflict = bool(detail.get("published") and item.get("published") and detail["published"] != item["published"])
    if conflict:
        doc["flags"].append("publication_date_conflict")
        doc["published_raw"] = json.dumps({"list": item["published"], "detail": detail["published"]})
    else:
        doc["published"] = detail.get("published") or item.get("published")
        doc["published_raw"] = detail.get("published_raw") or item.get("published_raw")
    doc["date_status"] = date_status(doc["published"], conflict, args.as_of, args.since, doc["published_raw"])
    doc["attachment_url"] = item.get("attachment_url") or detail.get("attachment_url")
    doc["body_status"] = detail.get("body_status", "not_fetched")
    reviewable = doc["date_status"] in REVIEW_STATES
    pdf = None
    if reviewable and doc["attachment_url"]:
        if args.meta_only:
            doc["attachment_status"] = "meta_only"
        elif publication.get("attachment_access") == "inbox":
            doc["attachment_status"] = "inbox_required"
        else:
            r = fetch_attachment(client, institution, item, doc["attachment_url"])
            doc["attachment_name"] = attachment_name(r.disposition)
            kind = sniff(r.data)
            raw_path = save_raw(args.data, r.data)
            if kind == "pdf":
                text, status, pages, flags = extract_pdf(r.data)
                doc["flags"] += flags
                matched = title_matches(doc["title"], text)
                if matched is False:
                    doc["flags"].append("attachment_title_mismatch")
                doc["attachment_status"] = "pdf_saved"
                doc["body_status"] = status
                pdf = (text, raw_path, "application/pdf", pages)
            else:
                doc["attachment_status"] = {"ole": "hwp_or_office_unsupported", "zip": "hwpx_or_office_unsupported"}.get(kind, "attachment_not_pdf")
    elif reviewable:
        doc["attachment_status"] = "no_attachment_found"
    ident = upsert_document(db, publication, doc)
    if html_version:
        add_version(db, ident, "html", *html_version)
    if pdf:
        add_version(db, ident, "pdf", *pdf)
    db.execute("INSERT INTO document_checks(publication_id,url,checked_at,status,detail) VALUES(?,?,?,?,?)",
               (publication["id"], item["url"], now(), doc["body_status"], ident))
    db.commit()
    emit(publication=publication["id"], id=ident, title=doc["title"], published=doc["published"],
         date_status=doc["date_status"], body_status=doc["body_status"], attachment=doc.get("attachment_status"))


def record_seen(db, publication, item, state):
    doc = dict(item, date_status=state, body_status="not_fetched", flags=[])
    upsert_document(db, publication, doc)


def collect(args, db, write):
    institutions, publications = selected(args)
    client = Client(args.timeout, args.delay)
    blocked = set()
    for publication in publications:
        institution = institutions[publication["institution"]]
        state = publication.get("status", "active")
        if state != "active" or "list" not in publication:
            emit(publication=publication["id"], status="skipped_" + state)
            continue
        if publication["institution"] in blocked:
            emit(publication=publication["id"], status="skipped_institution_blocked")
            continue
        stamp = now()
        try:
            r = client.get(institution, publication.get("list_url") or publication["url"])
            items = discover(publication, decode(r.data, r.charset), r.final)
        except Exception as e:
            if isinstance(e, Blocked):
                blocked.add(publication["institution"])
            db.execute("INSERT INTO checks(publication_id,checked_at,status,detail) VALUES(?,?,?,?)",
                       (publication["id"], stamp, "failed", type(e).__name__ + ": " + str(e)))
            db.commit()
            emit(publication=publication["id"], status="failed", error=str(e))
            continue
        known = {row[0] for row in db.execute("SELECT url FROM documents WHERE publication_id=?", (publication["id"],))}
        new = [item for item in items if item["url"] not in known]
        status = "listing_parsed" if items else "adapter_needs_review"
        db.execute("INSERT INTO checks(publication_id,checked_at,status,discovered,new,detail) VALUES(?,?,?,?,?,?)",
                   (publication["id"], stamp, status, len(items), len(new),
                    json.dumps({"final_url": r.final, "sample": items[:3]}, ensure_ascii=False)))
        db.commit()
        if not write:
            for item in items[:args.limit]:
                emit(publication=publication["id"], new=item["url"] not in known, title=item["title"],
                     published=item["published"], url=item["url"], attachment=item["attachment_url"])
            emit(publication=publication["id"], status=status, discovered=len(items), new=len(new))
            continue
        first_run = not known
        fetched = 0
        for position, item in enumerate(new):
            if first_run and position >= args.limit:
                # 첫 실행에서는 최신 몇 건만 읽고 나머지는 '이미 있던 글'로 기록해 둔다.
                record_seen(db, publication, item, "baseline")
                continue
            if date_status(item["published"], False, args.as_of, args.since, item["published_raw"]) == "outside_window":
                record_seen(db, publication, item, "outside_window")
                continue
            if fetched >= args.limit:
                break
            fetched += 1
            try:
                process(args, db, client, publication, institution, item)
            except Blocked as e:
                blocked.add(publication["institution"])
                emit(publication=publication["id"], url=item["url"], status="blocked", error=str(e))
                break
            except Exception as e:
                db.execute("INSERT INTO document_checks(publication_id,url,checked_at,status,detail) VALUES(?,?,?,?,?)",
                           (publication["id"], item["url"], now(), "failed", type(e).__name__ + ": " + str(e)))
                emit(publication=publication["id"], url=item["url"], status="failed", error=str(e))
        db.commit()
        emit(publication=publication["id"], status=status, discovered=len(items), new=len(new), fetched=fetched)


# ---------------------------------------------------------------- 동향 갱신용 내보내기

CHECK_LABEL = {"listing_parsed": "정상", "adapter_needs_review": "목록 확인 필요", "failed": "실패"}


def export_new(args, db):
    """정리 전 새 자료 목록을 공개용 JSON으로 쓴다. 내부 문서 id와 원문 본문은 넣지 않는다.

    --noted: 이미 노트를 썼거나 쓰지 않기로 한 문서 id 목록(JSON 배열). 이 목록의 문서는 뺀다.
    """
    if not args.out:
        raise ValueError("export-new needs --out")
    institutions, publications = load_sources()
    pubs = {p["id"]: p for p in publications}
    done = set(json.loads(args.noted.read_text(encoding="utf-8"))) if args.noted and args.noted.exists() else set()
    since = args.since
    items = []
    rows = db.execute("""SELECT * FROM documents WHERE date_status IN (?,?,?)
        ORDER BY COALESCE(published, substr(first_seen,1,10)) DESC, first_seen DESC""", REVIEW_STATES)
    for row in rows:
        if row["id"] in done or row["publication_id"] not in pubs:
            continue
        if (row["published"] or row["first_seen"][:10]) < since:
            continue
        pub = pubs[row["publication_id"]]
        items.append({"institution": institutions[pub["institution"]]["name"], "publication": pub["name"],
                      "title": row["title"], "published": row["published"], "url": row["url"],
                      "first_seen": row["first_seen"]})
    latest = {}
    for row in db.execute("SELECT publication_id, checked_at, status FROM checks ORDER BY checked_at"):
        if row["publication_id"] in pubs:
            latest[row["publication_id"]] = row
    by_inst = collections.OrderedDict()
    for pid, row in latest.items():
        name = institutions[pubs[pid]["institution"]]["name"]
        entry = by_inst.setdefault(name, {"institution": name, "checked_at": row["checked_at"], "problems": []})
        entry["checked_at"] = max(entry["checked_at"], row["checked_at"])
        if row["status"] != "listing_parsed":
            entry["problems"].append(pubs[pid]["name"] + " " + CHECK_LABEL.get(row["status"], row["status"]))
    out = {"updated_at": max((e["checked_at"] for e in by_inst.values()), default=None),
           "window_since": since, "items": items, "institutions": list(by_inst.values())}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    emit(out=str(args.out), items=len(items), institutions=len(by_inst))


# ---------------------------------------------------------------- 조회

ID_RE = r"[a-z]+-[0-9a-f]{12}"


def noted_ids():
    """노트 frontmatter의 db_id에 적힌 국내 문서 id (프로젝트 공통 규칙)."""
    ids = set()
    for path in (PROJECT / "notes").glob("**/*.md"):
        head = path.read_text(encoding="utf-8", errors="replace").split("---", 2)
        if len(head) < 3:
            continue
        m = re.search(r"^db_id:\s*[\"']?(" + ID_RE + r")[\"']?\s*$", head[1], re.M)
        if m:
            ids.add(m.group(1))
    return ids


def skipped_ids():
    """logs/collect/skipped_kr.tsv에 '노트 안 씀'으로 기록한 문서. 형식: db_id<TAB>날짜<TAB>사유"""
    path = PROJECT / "logs" / "collect" / "skipped_kr.tsv"
    if not path.exists():
        return set()
    return {line.split("\t", 1)[0].strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip()}


def pending(args, db):
    _, publications = load_sources()
    tiers = {p["id"]: p.get("tier") for p in publications}
    done = noted_ids() | skipped_ids()
    rows = db.execute("""SELECT d.*, v.page_count, v.raw_path FROM documents d LEFT JOIN versions v ON v.id=d.current_version
        WHERE d.date_status IN (?,?,?) ORDER BY d.published DESC""", REVIEW_STATES)
    for row in rows:
        if row["id"] in done:
            continue
        raw = "domestic_research/data/" + row["raw_path"] if row["raw_path"] else None
        emit(id=row["id"], publication=row["publication_id"], tier=tiers.get(row["publication_id"]), title=row["title"],
             published=row["published"], date_status=row["date_status"], body_status=row["body_status"],
             attachment=row["attachment_status"], attachment_url=row["attachment_url"], pages=row["page_count"],
             url=row["url"], raw_file=raw, flags=json.loads(row["quality_flags"] or "[]"))


def page_range(spec):
    m = re.fullmatch(r"(\d+)(?:-(\d+))?", spec or "")
    if not m:
        raise ValueError("--pages must look like 3 or 3-7")
    first = int(m.group(1))
    return first, int(m.group(2) or first)


def document_row(db, ident):
    row = db.execute("""SELECT d.*, v.text, v.raw_path, v.page_count, v.representation, v.id AS version_id
        FROM documents d LEFT JOIN versions v ON v.id=d.current_version WHERE d.id=?""", (ident,)).fetchone()
    if not row:
        raise ValueError("Document ID not found")
    return row


def inspect(args, db):
    row = document_row(db, args.id)
    meta = {k: row[k] for k in row.keys() if k != "text"}
    print(json.dumps(meta, ensure_ascii=False, indent=2))
    text = row["text"] or ""
    if args.pages:
        first, last = page_range(args.pages)
        parts = re.split(r"(?=\[PAGE \d+\]\n)", text)
        text = "".join(p for p in parts if re.match(r"\[PAGE (\d+)\]", p) and first <= int(re.match(r"\[PAGE (\d+)\]", p).group(1)) <= last)
    print("-----")
    print(text[:args.max_chars] if args.max_chars else text)


def squash(value):
    return re.sub(r"\s+", "", clean(value))


def evidence(args, db):
    if not all((args.claim, args.quote, args.kind)):
        raise ValueError("evidence requires --claim, --quote and --kind")
    row = document_row(db, args.id)
    text = row["text"] or ""
    if args.page is not None:
        if not row["page_count"] or not 1 <= args.page <= row["page_count"]:
            raise ValueError("Invalid PDF page")
        text = text.split("[PAGE %d]" % args.page, 1)[1].split("[PAGE ", 1)[0]
    # 한글 PDF는 추출할 때 띄어쓰기가 흔들리므로 공백을 지우고 비교한다.
    if squash(args.quote) not in squash(text):
        raise ValueError("Evidence quote is absent from this document/version/page")
    db.execute("INSERT INTO evidence(document_id,version_id,kind,claim,quote,page,created_at) VALUES(?,?,?,?,?,?,?)",
               (args.id, row["version_id"], args.kind, args.claim, args.quote, args.page, now()))
    db.commit()
    emit(status="evidence_attached", document_id=args.id, version_id=row["version_id"], page=args.page)


def attach(args, db):
    """사용자가 inbox/에 넣은 PDF를 기존 문서에 붙인다 (한국은행처럼 원문 자동 수집이 막힌 경우)."""
    row = document_row(db, args.id)
    path = Path(args.file).expanduser()
    data = path.read_bytes()
    if sniff(data) != "pdf":
        raise ValueError("Only PDF files can be attached")
    text, status, pages, flags = extract_pdf(data)
    matched = title_matches(row["title"], text)
    if matched is False and not args.force:
        raise ValueError("PDF title does not match the document title; check the file or pass --force")
    raw_path = save_raw(args.data, data)
    old_flags = json.loads(row["quality_flags"] or "[]")
    flags = sorted(set(old_flags + flags + (["attachment_title_mismatch"] if matched is False else [])))
    db.execute("UPDATE documents SET body_status=?, attachment_status=?, attachment_name=?, quality_flags=? WHERE id=?",
               (status, "attached_from_inbox", path.name, json.dumps(flags), args.id))
    version = add_version(db, args.id, "inbox_pdf", text, raw_path, "application/pdf", pages)
    db.commit()
    emit(status="attached", id=args.id, version_id=version, pages=pages, body_status=status, title_match=matched)


def status(args, db):
    _, publications = selected(args)
    for p in publications:
        row = db.execute("SELECT checked_at,status,discovered,new,detail FROM checks WHERE publication_id=? ORDER BY id DESC LIMIT 1", (p["id"],)).fetchone()
        counts = dict(db.execute("SELECT date_status,COUNT(*) FROM documents WHERE publication_id=? GROUP BY date_status", (p["id"],)).fetchall())
        last = dict(row) if row else None
        if last and last["status"] != "failed":
            last.pop("detail")
        emit(publication=p["id"], name=p["name"], state=p.get("status", "active"), last_check=last, documents=counts)


def search(args, db):
    like = "%" + args.query + "%"
    rows = db.execute("""SELECT d.id,d.publication_id,d.title,d.published,d.date_status,substr(v.text,1,300) AS excerpt
        FROM documents d LEFT JOIN versions v ON v.id=d.current_version
        WHERE d.title LIKE ? OR v.text LIKE ? ORDER BY d.published DESC LIMIT 50""", (like, like))
    for row in rows:
        emit(**dict(row))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("command", choices=["sources", "probe", "collect", "status", "pending", "search", "inspect", "evidence", "attach", "export-new"])
    p.add_argument("--source", help="쉼표로 구분한 간행물 id 또는 기관 id (예: kdi,bok_outlook)")
    p.add_argument("--data", type=Path, default=ROOT / "data")
    p.add_argument("--as-of", default=dt.date.today().isoformat())
    p.add_argument("--since", help="이 날짜 이전 발간물은 본문을 받지 않는다. 기본값은 --as-of 30일 전")
    p.add_argument("--limit", type=int, default=5, help="간행물별로 이번에 새로 읽을 최대 건수")
    p.add_argument("--delay", type=float, default=1.0, help="같은 사이트에 보내는 요청 사이의 최소 간격(초)")
    p.add_argument("--timeout", type=int, default=25)
    p.add_argument("--query", default="")
    p.add_argument("--id")
    p.add_argument("--pages", help="inspect에서 볼 PDF 쪽 범위. 예: 1-5")
    p.add_argument("--max-chars", type=int, default=0)
    p.add_argument("--kind", choices=["observed_fact", "author_judgment", "policy_proposal", "forecast"])
    p.add_argument("--claim")
    p.add_argument("--quote")
    p.add_argument("--page", type=int)
    p.add_argument("--file", help="attach에 쓸 PDF 경로 (보통 inbox/ 아래)")
    p.add_argument("--force", action="store_true", help="attach에서 제목 불일치를 무시한다")
    p.add_argument("--meta-only", action="store_true", help="collect에서 원문을 저장하지 않고 목록 정보만 남긴다")
    p.add_argument("--out", type=Path, help="export-new 결과 JSON 경로")
    p.add_argument("--noted", type=Path, help="export-new에서 뺄 문서 id 목록(JSON 배열)")
    args = p.parse_args()
    try:
        cutoff = dt.date.fromisoformat(args.as_of)
        args.since = args.since or (cutoff - dt.timedelta(days=30)).isoformat()
        if dt.date.fromisoformat(args.since) > cutoff or args.limit < 1 or args.delay < 0.5:
            raise ValueError("Invalid date window, limit or delay (delay must be at least 0.5s)")
        if args.command == "sources":
            institutions, publications = selected(args)
            for pub in publications:
                emit(id=pub["id"], institution=institutions[pub["institution"]]["name"], name=pub["name"],
                     status=pub.get("status", "active"), tier=pub.get("tier"), cadence=pub.get("cadence"),
                     attachment=pub.get("attachment_access"), url=pub["url"])
            return
        db = connect(args.data)
        if args.command in ("probe", "collect"):
            collect(args, db, write=args.command == "collect")
        else:
            {"status": status, "pending": pending, "search": search, "inspect": inspect,
             "evidence": evidence, "attach": attach, "export-new": export_new}[args.command](args, db)
        db.close()
    except (ValueError, sqlite3.Error, OSError) as e:
        p.error(str(e))


if __name__ == "__main__":
    main()
