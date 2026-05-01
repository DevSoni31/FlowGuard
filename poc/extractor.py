"""
extractor.py — Phase 1: Code → FlowGuard Spec
Strategy:
  1. AST + regex detects capabilities from code patterns.
  2. If GEMINI_API_KEY is set, Gemini refines the spec.
  3. Returns Agent + metadata for the verifier.
"""
import ast, re, os, json
from pathlib import Path
from hyperedges import Agent, ALL_CAPS

CAP_SIGNATURES = {
    "webSearch":     [r"requests\.get", r"httpx\.", r"aiohttp\.", r"search\(", r"tavily", r"serpapi", r"web_search"],
    "codeExec":      [r"subprocess\.", r"exec\(", r"eval\(", r"os\.system", r"code_interpreter", r"python_repl"],
    "fileRead":      [r"open\(.+['\"]r", r"\.read\(\)", r"pathlib.*read_text", r"read_file", r"os\.listdir"],
    "networkAccess": [r"requests\.post", r"socket\.", r"paramiko", r"upload", r"\.connect\("],
    "shellExec":     [r"subprocess\.run", r"subprocess\.Popen", r"shell=True", r"bash\("],
    "databaseQuery": [r"sqlite3", r"psycopg", r"sqlalchemy", r"\.execute\(", r"cursor\."],
    "readDB":        [r"db\.get", r"\.fetchall", r"\.fetchone", r"redis\.get", r"SELECT\s+"],
    "emailSend":     [r"smtplib", r"sendgrid", r"send_email", r"SMTP\(", r"sendmail"],
    "sendEmail":     [r"smtplib", r"SMTP\("],
}

UNIVERSALLY_FORBIDDEN = {"exfilData", "privEsc", "dataLeak", "remoteExec"}

def detect_caps_ast(source: str, filepath: str) -> set:
    detected = set()
    for cap, patterns in CAP_SIGNATURES.items():
        for p in patterns:
            if re.search(p, source, re.IGNORECASE):
                detected.add(cap)
                break
    fname = Path(filepath).stem.lower()
    if any(k in fname for k in ["web","search","scrape","fetch"]):   detected.add("webSearch")
    if any(k in fname for k in ["exec","run","code","shell"]):       detected.add("codeExec")
    if any(k in fname for k in ["file","read","load","ingest"]):     detected.add("fileRead")
    if any(k in fname for k in ["email","mail","notify"]):           detected.add("emailSend")
    if any(k in fname for k in ["db","database","sql","query"]):     detected.add("databaseQuery"); detected.add("readDB")
    if any(k in fname for k in ["api","http","network","post"]):     detected.add("networkAccess")
    return detected

def refine_with_gemini(source: str, filepath: str, ast_caps: set) -> dict | None:
    api_key = os.getenv("GEMINI_API_KEY", "")
    if not api_key:
        return None
    try:
        import google.generativeai as genai
        genai.configure(api_key=api_key)
        model = genai.GenerativeModel("gemini-1.5-flash")
        cap_list = sorted(ALL_CAPS)
        prompt = f"""You are a security analyst for AI agent pipelines.

Extract a FlowGuard capability specification from this Python agent code.

AVAILABLE CAPABILITIES: {cap_list}

RULES:
- base = capabilities this agent actively uses
- forbidden = capabilities it must never produce (always include: exfilData, privEsc, dataLeak, remoteExec)
- data_label = sensitivity of data handled: "low" | "medium" | "high"
- pipeline_channels = data-flow channels if multi-step: [{{"name":"..","src":"..","dst":".."}}]
- cedar_policies = per-agent Cedar policies: [{{"principal":"agent-name","action":"cap-name"}}]

AST pre-detected: {sorted(ast_caps)}
FILE: {filepath}

CODE:
```python
{source[:3000]}
```

Respond ONLY with valid JSON:
{{"base":[],"forbidden":[],"data_label":"low","pipeline_channels":[],"cedar_policies":[],"agent_description":""}}"""
        resp = model.generate_content(prompt)
        text = re.sub(r"^```json\s*|\s*```$", "", resp.text.strip())
        return json.loads(text)
    except Exception:
        return None

def extract_spec(filepath: str) -> dict:
    path   = Path(filepath)
    source = path.read_text()
    aname  = path.stem.replace("_", "-")
    ast_caps = detect_caps_ast(source, filepath)
    llm = refine_with_gemini(source, filepath, ast_caps)
    method = "llm" if llm else "ast"

    if llm:
        base      = frozenset(llm.get("base", sorted(ast_caps)))
        forbidden = frozenset(list(llm.get("forbidden", [])) + list(UNIVERSALLY_FORBIDDEN))
        data_label = llm.get("data_label", "low")
        pipeline   = llm.get("pipeline_channels", [])
        cedar_pols = llm.get("cedar_policies", [{"principal": aname, "action": c} for c in sorted(base)])
        description = llm.get("agent_description", f"Extracted from {path.name}")
    else:
        base       = frozenset(ast_caps)
        forbidden  = frozenset(UNIVERSALLY_FORBIDDEN | {c for c in {"shellExec","codeExec","networkAccess"} if c not in ast_caps})
        src_lower  = source.lower()
        data_label = "high" if any(k in src_lower for k in ["patient","medical","hipaa","phi"]) else \
                     "medium" if any(k in src_lower for k in ["summary","internal","report"]) else "low"
        pipeline   = []
        cedar_pols = [{"principal": aname, "action": c} for c in sorted(base)]
        description = f"Extracted from {path.name} via AST analysis"

    return {
        "agent":             Agent(aname, base, forbidden),
        "data_label":        data_label,
        "pipeline_channels": pipeline,
        "cedar_policies":    cedar_pols,
        "description":       description,
        "method":            method,
        "filepath":          str(filepath),
        "raw_source":        source,
    }