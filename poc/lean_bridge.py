"""
lean_bridge.py
Bridges the Python PoC to the actual Lean 4 project in this repo.

What it does:
  1. run_lake_build()     — calls `lake build` in the repo root, captures output
  2. eval_lean_expr()     — evaluates a Lean expression using `lake env lean --run`
  3. extract_theorems()   — reads your .lean files and pulls out theorem names + statements
  4. verify_demo_agents() — runs the canonical FlowGuard checks inside Lean itself
"""

import subprocess, re, os
from pathlib import Path

# ── Path resolution ───────────────────────────────────────────────────────────
# poc/ sits inside the repo root, so lean root is one level up
REPO_ROOT  = Path(__file__).parent.parent.resolve()   # FlowGuard/
LEAN_DIR   = REPO_ROOT / "FlowGuard"                  # FlowGuard/FlowGuard/
LEAN_FILES = list(LEAN_DIR.glob("*.lean"))

# ── 1. Build ──────────────────────────────────────────────────────────────────
def run_lake_build(timeout: int = 1800) -> dict:
    """
    Runs `lake build` with live streaming output.
    timeout=1800 = 30 minutes, covers worst-case cold builds.
    Shows [N/M] progress lines as they appear, exactly like the terminal does.
    """
    import sys
    try:
        proc = subprocess.Popen(
            ["lake", "build"],
            cwd=REPO_ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,   # merge stderr into stdout for unified stream
            text=True,
            bufsize=1,
        )

        all_output = []
        errors     = []

        import time
        start = time.time()

        for line in proc.stdout:
            line_stripped = line.rstrip()
            all_output.append(line_stripped)

            # Print progress live — [N/M] lines, errors, warnings
            if any(marker in line_stripped for marker in ["[", "error:", "warning:", "Build completed", "✓", "✗"]):
                print(f"  {line_stripped}", flush=True)

            if "error:" in line_stripped.lower():
                errors.append(line_stripped)

            # Manual timeout guard
            if time.time() - start > timeout:
                proc.kill()
                return {"success": False, "output": "\n".join(all_output),
                        "errors": ["lake build exceeded timeout — run `lake build` manually first"]}

        proc.wait()
        success = proc.returncode == 0
        return {
            "success": success,
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
    lean_src = f"{imports}\n\n{expression}\n"
    tmp = REPO_ROOT / "_poc_eval.lean"
    try:
        tmp.write_text(lean_src)
        result = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            cwd=REPO_ROOT,
            capture_output=True, text=True, timeout=60
        )
        tmp.unlink(missing_ok=True)
        output = result.stdout.strip()
        return {"success": result.returncode == 0, "value": output}
    except Exception as e:
        tmp.unlink(missing_ok=True)
        return {"success": False, "value": str(e)}

# ── 3. Extract theorems from .lean source files ───────────────────────────────
_THEOREM_RE = re.compile(
    r'(?:^|\n)(theorem|lemma)\s+(\w+)'   # name
    r'(.*?)'                              # statement (lazy)
    r'\s*:=',                            # ends at :=
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
        # Trim to first 300 chars to keep it readable
        statement = re.sub(r'\s+', ' ', raw_stmt)[:300]
        # Look for a docstring immediately before
        before   = source[:m.start()]
        doc_m    = _DOC_RE.search(before[-300:])
        docstring = doc_m.group(1).strip() if doc_m else ""
        # Approximate line number
        line = source[:m.start()].count('\n') + 1
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

# ── 4. Run the canonical demo checks inside Lean ──────────────────────────────
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
        "label":      "Cedar denies exfilData for webAgent",
        "expression": '#eval cedarEval teamPolicy { principal := { name := "webAgent" }, action := { name := "exfilData" }, resource := { name := "net" } }',
        "imports":    "import FlowGuard.CedarBridge",
        "expected":   "Decision.deny",
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

def verify_demo_in_lean() -> list[dict]:
    """
    Runs each demo check in your actual Lean environment.
    Returns list of {"label", "passed", "value", "theorem", "lean_output"}.
    Falls back gracefully if Lean is not installed.
    """
    results = []
    for check in DEMO_CHECKS:
        out = eval_lean_expr(check["expression"], check["imports"])
        passed = check["expected"].lower() in out["value"].lower() if out["success"] else False
        results.append({
            "label":        check["label"],
            "passed":       passed,
            "value":        out["value"],
            "theorem":      check["theorem"],
            "lean_output":  out["value"],
            "lean_success": out["success"],
        })
    return results