"""
extractor.py — Phase 1: Code → FlowGuard Spec

Extraction modes (chosen interactively at runtime):
  ast  — regex + filename heuristics only, fully offline
  llm  — Gemini 2.5 Flash Lite refines the AST result
  both — AST runs first, LLM refines, differences are shown
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

# These are ALWAYS forbidden — this set never varies between runs
UNIVERSALLY_FORBIDDEN = frozenset({"exfilData", "privEsc", "dataLeak", "remoteExec"})

def detect_caps_ast(source: str, filepath: str) -> set:
    detected = set()
    for cap, patterns in CAP_SIGNATURES.items():
        for p in patterns:
            if re.search(p, source, re.IGNORECASE):
                detected.add(cap)
                break
    fname = Path(filepath).stem.lower()
    if any(k in fname for k in ["web", "search", "scrape", "fetch"]):  detected.add("webSearch")
    if any(k in fname for k in ["exec", "run", "code", "shell"]):      detected.add("codeExec")
    if any(k in fname for k in ["file", "read", "load", "ingest"]):    detected.add("fileRead")
    if any(k in fname for k in ["email", "mail", "notify"]):           detected.add("emailSend")
    if any(k in fname for k in ["db", "database", "sql", "query"]):    detected.add("databaseQuery"); detected.add("readDB")
    if any(k in fname for k in ["api", "http", "network", "post"]):    detected.add("networkAccess")
    return detected

def refine_with_gemini(source: str, filepath: str, ast_caps: set) -> dict | None:
    """Calls Gemini 2.5 Flash Lite using the new google-genai SDK."""
    api_key = os.getenv("GEMINI_API_KEY", "")
    if not api_key:
        return None
    try:
        from google import genai
        from google.genai import types
        client = genai.Client(api_key=api_key)

        cap_list = sorted(ALL_CAPS)
        aname = Path(filepath).stem.replace("_", "-")
        prompt = f"""You are a security analyst for AI agent pipelines.

Extract a FlowGuard capability specification from this Python agent code.

AVAILABLE CAPABILITIES: {cap_list}

RULES:
- base = list of capabilities this agent actively uses (strings from the list above)
- forbidden = MUST include exactly: ["exfilData", "privEsc", "dataLeak", "remoteExec"] plus any others that are dangerous for this specific agent
- data_label = sensitivity of data handled: "low" | "medium" | "high"
- pipeline_channels = data-flow channels if multi-step: [{{"name":"..","src":"..","dst":".."}}] — empty list if single agent
- cedar_policies = per-agent Cedar allow policies: [{{"principal":"{aname}","action":"cap-name"}}] — one entry per base capability
- agent_description = one sentence describing what this agent does and its risk profile

AST pre-detected base capabilities: {sorted(ast_caps)}
FILE: {filepath}

CODE:
```python
{source[:3000]}
```

Respond ONLY with valid JSON, no markdown fences:
{{"base":[],"forbidden":[],"data_label":"low","pipeline_channels":[],"cedar_policies":[],"agent_description":""}}"""

        response = client.models.generate_content(
            model="gemini-2.5-flash-lite",
            contents=prompt,
            config=types.GenerateContentConfig(
                temperature=0.0,   # deterministic — no variation between runs
                max_output_tokens=1024,
            )
        )
        text = response.text.strip()
        # Strip any accidental markdown fences
        text = re.sub(r"^```json\s*|\s*```$", "", text, flags=re.MULTILINE).strip()
        return json.loads(text)
    except Exception as e:
        return None  # falls back to AST silently

def _build_spec_from_ast(source: str, filepath: str, ast_caps: set) -> dict:
    """Pure AST-based spec. forbidden is always UNIVERSALLY_FORBIDDEN + non-base dangerous caps."""
    aname = Path(filepath).stem.replace("_", "-")
    src_lower = source.lower()
    # Forbidden = universal set + any dangerous caps this agent doesn't use
    dangerous = {"shellExec", "codeExec", "networkAccess", "databaseQuery", "emailSend"}
    extra_forbidden = dangerous - ast_caps
    forbidden = UNIVERSALLY_FORBIDDEN | extra_forbidden
    data_label = (
        "high"   if any(k in src_lower for k in ["patient", "medical", "hipaa", "phi"]) else
        "medium" if any(k in src_lower for k in ["summary", "internal", "report"]) else
        "low"
    )
    cedar_pols = [{"principal": aname, "action": c} for c in sorted(ast_caps)]
    return {
        "base":              frozenset(ast_caps),
        "forbidden":         frozenset(forbidden),
        "data_label":        data_label,
        "pipeline_channels": [],
        "cedar_policies":    cedar_pols,
        "description":       f"Extracted from {Path(filepath).name} via AST analysis",
    }

def _build_spec_from_llm(llm: dict, ast_caps: set, filepath: str) -> dict:
    """LLM-based spec. Always merges UNIVERSALLY_FORBIDDEN into forbidden."""
    aname = Path(filepath).stem.replace("_", "-")
    base     = frozenset(llm.get("base", sorted(ast_caps)))
    # ALWAYS include the universal forbidden set — LLM cannot reduce it
    forbidden = UNIVERSALLY_FORBIDDEN | frozenset(llm.get("forbidden", []))
    cedar_pols = llm.get("cedar_policies") or [{"principal": aname, "action": c} for c in sorted(base)]
    return {
        "base":              base,
        "forbidden":         forbidden,
        "data_label":        llm.get("data_label", "low"),
        "pipeline_channels": llm.get("pipeline_channels", []),
        "cedar_policies":    cedar_pols,
        "description":       llm.get("agent_description", f"Extracted from {Path(filepath).name}"),
    }

def extract_spec(filepath: str, mode: str = "ast") -> dict:
    """
    mode: "ast" | "llm" | "both"
    Returns the standard spec dict consumed by verifier.py
    """
    path   = Path(filepath)
    source = path.read_text()
    aname  = path.stem.replace("_", "-")

    ast_caps = detect_caps_ast(source, filepath)
    ast_spec = _build_spec_from_ast(source, filepath, ast_caps)

    if mode == "ast":
        return {
            "agent":             Agent(aname, ast_spec["base"], ast_spec["forbidden"]),
            "data_label":        ast_spec["data_label"],
            "pipeline_channels": ast_spec["pipeline_channels"],
            "cedar_policies":    ast_spec["cedar_policies"],
            "description":       ast_spec["description"],
            "method":            "ast",
            "filepath":          str(filepath),
            "raw_source":        source,
        }

    # LLM or both — call Gemini
    llm = refine_with_gemini(source, filepath, ast_caps)

    if mode == "llm" and not llm:
        # Gemini unavailable — fall back to AST silently
        spec = ast_spec
        method = "ast (fallback)"
    elif mode == "llm":
        spec   = _build_spec_from_llm(llm, ast_caps, filepath)
        method = "llm"
    else:  # both
        if llm:
            llm_spec = _build_spec_from_llm(llm, ast_caps, filepath)
            # Merge: union of base, union of forbidden (most conservative)
            merged_base     = frozenset(ast_spec["base"] | llm_spec["base"])
            merged_forbidden = frozenset(ast_spec["forbidden"] | llm_spec["forbidden"])
            spec = {
                "base":              merged_base,
                "forbidden":         merged_forbidden,
                "data_label":        llm_spec["data_label"],
                "pipeline_channels": llm_spec["pipeline_channels"],
                "cedar_policies":    llm_spec["cedar_policies"],
                "description":       f"[AST+LLM] {llm_spec['description']}",
            }
            method = "both"
        else:
            spec   = ast_spec
            method = "ast (llm unavailable)"

    return {
        "agent":             Agent(aname, spec["base"], spec["forbidden"]),
        "data_label":        spec["data_label"],
        "pipeline_channels": spec["pipeline_channels"],
        "cedar_policies":    spec["cedar_policies"],
        "description":       spec["description"],
        "method":            method,
        "filepath":          str(filepath),
        "raw_source":        source,
    }