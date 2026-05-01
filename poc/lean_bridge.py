"""
lean_bridge.py
Bridges the Python PoC to the actual Lean 4 project in this repo.

What it does:
  1. run_lake_build()      — calls `lake build` in the repo root, captures output
  2. eval_lean_expr()      — evaluates a Lean expression using `lake env lean --run`
  3. extract_theorems()    — reads your .lean files and pulls out theorem names + statements
  4. verify_demo_in_lean() — runs the canonical FlowGuard checks inside Lean itself
"""

import subprocess, re, os
from pathlib import Path

# ── Path resolution ───────────────────────────────────────────────────────────
REPO_ROOT  = Path(__file__).parent.parent.resolve()   # FlowGuard/
LEAN_DIR   = REPO_ROOT / "FlowGuard"                  # FlowGuard/FlowGuard/
LEAN_FILES = list(LEAN_DIR.glob("*.lean"))

# ── 1. Build ──────────────────────────────────────────────────────────────────
def run_lake_build(timeout: int = 1800) -> dict:
    """
    Runs `lake build` with live streaming output.
    timeout=1800 = 30 minutes, covers worst-case cold builds.
    """
    import sys, time
    try:
        proc = subprocess.Popen(
            ["lake", "build"],
            cwd=REPO_ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        all_output = []
        errors     = []
        start = time.time()
        for line in proc.stdout:
            line_stripped = line.rstrip()
            all_output.append(line_stripped)
            if any(marker in line_stripped for marker in ["[", "error:", "warning:", "Build completed", "✓", "✗"]):
                print(f"  {line_stripped}", flush=True)
            if "error:" in line_stripped.lower():
                errors.append(line_stripped)
            if time.time() - start > timeout:
                proc.kill()
                return {"success": False, "output": "\n".join(all_output),
                        "errors": ["lake build exceeded timeout — run `lake build` manually first"]}
        proc.wait()
        return {
            "success": proc.returncode == 0,
            "output":  "\n".join(all_output),
            "errors":  errors,
        }
    except FileNotFoundError:
        return {"success": False, "output": "",
                "errors": ["lake not found — is Lean 4 installed? Use --skip-lean to bypass."]}

# ── 2. Evaluate a Lean expression ─────────────────────────────────────────────
def eval_lean_expr(expression: str, imports: str = "import FlowGuard.CapHypergraph") -> dict:
    """
    Evaluates a Lean expression by writing a temporary .lean file and running it.
    Example:
        eval_lean_expr("#eval isCapSafe demoEdges webAgent")
    Returns {"success": bool, "value": str}
    """
    # FIX 1: open FlowGuard so bare names resolve without namespace prefix
    lean_src = f"{imports}\n\nopen FlowGuard\n\n{expression}\n"
    tmp = REPO_ROOT / "_poc_eval.lean"   # FIX 2: hoisted above try — always defined in except
    try:
        tmp.write_text(lean_src)
        result = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            cwd=REPO_ROOT,
            capture_output=True, text=True, timeout=60
        )
        tmp.unlink(missing_ok=True)
        return {"success": result.returncode == 0, "value": result.stdout.strip()}
    except Exception as e:
        tmp.unlink(missing_ok=True)
        return {"success": False, "value": str(e)}

# ── 3. Extract theorems from .lean source files ───────────────────────────────
_THEOREM_RE = re.compile(
    r'(?:^|\n)(theorem|lemma)\s+(\w+)'
    r'(.*?)'
    r'\s*:=',
    re.DOTALL
)
_DOC_RE = re.compile(r'/--\s*(.*?)\s*-/', re.DOTALL)

def extract_theorems(lean_file: Path) -> list[dict]:
    """
    Reads a .lean file and extracts all theorem/lemma declarations.
    Returns list of {"name", "statement", "docstring", "file", "line"}.
    """
    source = lean_file.read_text()
    results = []
    for m in _THEOREM_RE.finditer(source):
        name      = m.group(2)
        raw_stmt  = (m.group(3) or "").strip()
        statement = re.sub(r'\s+', ' ', raw_stmt)[:300]
        before    = source[:m.start()]
        doc_m     = _DOC_RE.search(before[-300:])
        docstring = doc_m.group(1).strip() if doc_m else ""
        line      = source[:m.start()].count('\n') + 1
        results.append({
            "name":      name,
            "statement": statement,
            "docstring": docstring,
            "file":      lean_file.name,
            "line":      line,
        })
    return results

def get_all_theorems() -> dict[str, list]:
    """Returns {filename: [theorem_dicts]} for all .lean files."""
    return {f.name: extract_theorems(f) for f in LEAN_FILES}

# ── 4. Module-level check descriptors (metadata only — not iterated at runtime) ──
# FIX 3: corrected principal "web-agent", resource "server", expected "CedarDecision.deny"
DEMO_CHECKS = [
    {
        "label":      "webAgent is individually safe",
        "expression": '#eval isCapSafe demoEdges webAgent',
        "imports":    "import FlowGuard.CapHypergraph",
        "expected":   "true",
        "theorem":    "webAgent_is_safe",
    },
    {
        "label":      "execAgent is individually safe",
        "expression": '#eval isCapSafe demoEdges execAgent',
        "imports":    "import FlowGuard.CapHypergraph",
        "expected":   "true",
        "theorem":    "execAgent_is_safe",
    },
    {
        "label":      "Composed team is UNSAFE",
        "expression": '#eval isCapSafe demoEdges (compose webAgent execAgent)',
        "imports":    "import FlowGuard.CapHypergraph",
        "expected":   "false",
        "theorem":    "composedTeam_is_unsafe",
    },
    {
        "label":      "Cedar denies exfilData for web-agent",
        "expression": '#eval cedarEval teamPolicy { principal := { name := "web-agent" }, action := { name := "exfilData" }, resource := { name := "server" } }',
        "imports":    "import FlowGuard.CedarBridge",
        "expected":   "CedarDecision.deny",
        "theorem":    "cedar_nonCompositionality_gap",
    },
    {
        "label":      "capClosure is a fixed point",
        "expression": '#check @capClosure_is_fixpoint',
        "imports":    "import FlowGuard.CapHypergraph",
        "expected":   "capClosure_is_fixpoint",
        "theorem":    "capClosure_is_fixpoint",
    },
]

# ── 5. Run all canonical demo checks inside Lean in one subprocess ────────────
def verify_demo_in_lean() -> list[dict]:
    """
    Writes ONE .lean file with all #eval / #check calls, runs it ONCE.
    Much faster than five separate subprocess calls.
    Falls back gracefully if Lean is not installed or times out.

    Fix log:
      - FIX 4: Added `open FlowGuard` — resolves isCapSafe, webAgent, compose,
               cedarEval, teamPolicy, capClosure_is_fixpoint without namespace prefix.
      - FIX 5: Principal "webAgent" → "web-agent", resource "net" → "server"
               (must match string literals in webPolicy / teamPolicy in CedarBridge.lean).
      - FIX 6: expected "deny" → "CedarDecision.deny" (Lean prints full constructor).
      - FIX 7: tmp hoisted above try — always defined when except branches run.
    """
    lean_src = """\
import FlowGuard.CapHypergraph
import FlowGuard.CedarBridge

open FlowGuard

#eval isCapSafe demoEdges webAgent
#eval isCapSafe demoEdges execAgent
#eval isCapSafe demoEdges (compose webAgent execAgent)
#eval cedarEval teamPolicy { principal := { name := "web-agent" }, action := { name := "exfilData" }, resource := { name := "server" } }
#check @capClosure_is_fixpoint
"""
    tmp = REPO_ROOT / "_poc_eval.lean"   # FIX 7: hoisted above try
    tmp.write_text(lean_src)

    CHECKS = [
        {"label": "webAgent is individually safe",    "theorem": "webAgent_is_safe",              "expected": "true"},
        {"label": "execAgent is individually safe",   "theorem": "execAgent_is_safe",             "expected": "true"},
        {"label": "Composed team is UNSAFE",          "theorem": "composedTeam_is_unsafe",        "expected": "false"},
        {"label": "Cedar denies exfilData",           "theorem": "cedar_nonCompositionality_gap", "expected": "CedarDecision.deny"},
        {"label": "capClosure is a fixed point",      "theorem": "capClosure_is_fixpoint",        "expected": "capClosure_is_fixpoint"},
    ]

    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            cwd=REPO_ROOT,
            capture_output=True, text=True,
            timeout=1800   # 30 minutes — covers cold elaboration on Windows
        )
        tmp.unlink(missing_ok=True)

        lines = [l.strip() for l in result.stdout.splitlines() if l.strip()]
        results = []
        for i, check in enumerate(CHECKS):
            value  = lines[i] if i < len(lines) else ""
            passed = check["expected"].lower() in value.lower()
            results.append({
                "label":        check["label"],
                "passed":       passed,
                "value":        value,
                "theorem":      check["theorem"],
                "lean_output":  value,
                "lean_success": result.returncode == 0,
            })
        return results

    except subprocess.TimeoutExpired:
        tmp.unlink(missing_ok=True)
        return [{"label": c["label"], "passed": False, "value": "timed out",
                 "theorem": c["theorem"], "lean_output": "", "lean_success": False}
                for c in CHECKS]
    except FileNotFoundError:
        tmp.unlink(missing_ok=True)
        return []