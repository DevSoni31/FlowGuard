"""
analyze.py — FlowGuard PoC main entry point.
Usage:
  python analyze.py agent1.py agent2.py [agent3.py ...]
  python analyze.py --demo          # runs the canonical webAgent + execAgent demo
  python analyze.py --medical-demo  # runs the medical pipeline IFC demo
"""

from lean_bridge import run_lake_build, verify_demo_in_lean, get_all_theorems
import sys, os, argparse, webbrowser
from pathlib import Path
from rich.console import Console
from rich.panel import Panel
from rich.table import Table
from rich.progress import track
from rich import box
import dotenv

dotenv.load_dotenv()

from extractor import extract_spec
from verifier  import verify_pipeline

console = Console()

DEMO_AGENTS   = ["sample_agents/web_search_agent.py", "sample_agents/code_exec_agent.py"]

def print_banner():
    console.print(Panel.fit(
        "[bold cyan]FlowGuard PoC[/]\n"
        "[italic]Code → Spec → Verify — Mathematical safety for multi-agent AI[/]\n"
        "[dim]Powered by Lean 4 proofs · CapHypergraph · InfoFlow · CedarBridge[/]",
        border_style="cyan"
    ))

def print_extraction(specs: list):
    console.rule("[bold blue][1/3] Capability Extraction[/]")
    for s in specs:
        a = s["agent"]
        badge = "[bold green]LLM[/]" if s["method"] == "llm" else "[bold yellow]AST[/]"
        console.print(f"\n  {badge} [bold]{a.name}[/]  [dim]{s['filepath']}[/]")
        console.print(f"       base:      [cyan]{sorted(a.base)}[/]")
        console.print(f"       forbidden: [red]{sorted(a.forbidden)}[/]")
        console.print(f"       label:     [magenta]{s['data_label']}[/]")
        console.print(f"       [dim]{s['description']}[/]")

def print_individual_checks(result: dict):
    console.rule("[bold blue][2/3] Individual Safety Checks — isCapSafe[/]")
    for ag in result["individual"]:
        badge = "[bold green]✓ SAFE[/]" if ag["safe"] else "[bold red]✗ UNSAFE[/]"
        console.print(f"\n  {badge}  [bold]{ag['name']}[/]")
        console.print(f"    emergent caps: [cyan]{ag['emergent']}[/]")
        if not ag["safe"]:
            console.print(
                f"    [bold yellow]⚠  This agent is unsafe IN ISOLATION — before any composition.[/]\n"
                f"    [dim]The Lean-proven minimal counterexample requires two individually-safe agents.[/]\n"
                f"    [dim]This real-world agent is a strictly worse case: emergence fires with a single agent.[/]\n"
                f"    [dim]Theorem: nonCompositionality_universal (CapHypergraph.lean) still applies —[/]\n"
                f"    [dim]the universal theorem covers this as the degenerate single-agent case.[/]"
            )

def print_composition_result(result: dict):
    console.rule("[bold blue][3/3] Composition — FlowGuard Verdict[/]")
    c = result["composed"]
    verdict = result["verdict"]

    if verdict == "UNSAFE":
        console.print(Panel(
            f"[bold red]✗ UNSAFE — Emergent capability detected[/]\n\n"
            + "\n".join(f"  [yellow]⚡ {e['label']}[/]" for e in result["fired_edges"]),
            title="[bold red]COMPOSITION RESULT[/]", border_style="red"
        ))
    else:
        console.print(Panel(
            "[bold green]✓ SAFE — No forbidden capabilities emerge from composition[/]",
            title="[bold green]COMPOSITION RESULT[/]", border_style="green"
        ))

    console.print(f"\n  composed base:     [cyan]{c['base']}[/]")
    console.print(f"  composed emergent: [yellow]{c['emergent']}[/]")
    console.print(f"  forbidden:         [red]{c['forbidden']}[/]")

def print_cedar_panel(result: dict):
    cedar = result["cedar"]
    if not cedar["blind_spot"]:
        return
    console.rule("[bold magenta]Cedar vs FlowGuard — The Blind Spot[/]")
    console.print(Panel(
        "[bold]Cedar evaluates each (principal, action) in isolation.[/]\n\n"
        "[green]Cedar says:[/] exfilData → DENY for every individual agent ✓\n"
        "[red]FlowGuard says:[/] composed team CAN exfiltrate — emergence detected ✗\n\n"
        f"[dim]{cedar['explanation']}[/]\n\n"
        "[bold cyan]Theorem:[/] cedar_nonCompositionality_gap (CedarBridge.lean)",
        title="[bold magenta]Cedar's Structural Blind Spot[/]",
        border_style="magenta"
    ))

def print_ifc_panel(result: dict):
    ifc = result["ifc"]
    if ifc["transitive_safe"] is None:
        return
    console.rule("[bold blue]Information Flow Check — InfoFlow[/]")
    t_badge = "[green]✓ SAFE[/]" if ifc["transitive_safe"]  else "[red]✗ UNSAFE[/]"
    h_badge = "[green]✓ SAFE[/]" if ifc["hopwise_safe"]     else "[red]✗ UNSAFE[/]"
    console.print(f"  isTransitivelySafe (endpoint check): {t_badge}")
    console.print(f"  isHopwiseSafe      (per-hop check):  {h_badge}")
    if not ifc["hopwise_safe"] and ifc["transitive_safe"]:
        console.print("\n  [yellow]⚠ WARNING:[/] Endpoint check passed but an intermediate hop violates the lattice.")
        console.print("  [dim]Theorem: transitive_safety_misses_intermediate (InfoFlow.lean)[/]")

def print_theorems(result: dict, all_theorems: dict = None):
    if not result["theorems_cited"]:
        return
    console.rule("[bold cyan]Theorems Cited — read from FlowGuard/*.lean[/]")
    for t in result["theorems_cited"]:
        console.print(f"\n  [bold cyan]{t['name']}[/]  [dim]{t['file']}[/]")

        # Try to find the real theorem text from the parsed .lean file
        real_stmt = None
        if all_theorems:
            file_theorems = all_theorems.get(t["file"], [])
            match = next((th for th in file_theorems if th["name"] == t["name"]), None)
            if match:
                real_stmt = match["statement"]
                if match.get("docstring"):
                    console.print(f"  [dim]doc: {match['docstring'][:120]}[/]")

        stmt = real_stmt or t["statement"]
        console.print(f"  [dim italic]{stmt[:400]}[/]")
        console.print(f"  → {t['english']}")
        if real_stmt:
            console.print(f"  [dim green]  ↑ text read directly from {t['file']}[/]")

def print_lean_verification(lean_checks: list):
    if not lean_checks:
        return
    console.rule("[bold green]Lean Kernel Verification — verify_demo_in_lean()[/]")
    for check in lean_checks:
        if check.get("lean_success") is False and "not found" in check.get("value", ""):
            badge = "[dim]─ skipped[/]"
        elif check.get("passed"):
            badge = "[bold green]✓[/]"
        else:
            badge = "[bold red]✗[/]"
        console.print(f"  {badge}  [bold]{check['label']}[/]")
        console.print(f"       theorem:  [cyan]{check['theorem']}[/]")
        if check.get("value"):
            lean_out = check['value'].replace("FlowGuard.", "")
            console.print(f"       lean out: [dim]{lean_out[:120]}[/]")

def launch_dashboard():
    """Open the static FlowGuard demo page directly in the browser."""
    # Keep the dashboard template in poc/templates and resolve from this file's directory.
    html_path = Path(__file__).resolve().parent / "templates" / "flowguard-page.html"
    if not html_path.exists():
        console.print(f"[yellow]⚠ Dashboard page not found at {html_path}[/]")
        console.print("[dim]Expected location: poc/templates/flowguard-page.html[/]")
        return
    input("\n  Press Enter to open the summary page in your browser...")
    webbrowser.open(html_path.as_uri())
    console.print(f"\n[bold cyan]Dashboard opened in browser.[/]")
    console.print(f"[dim]({html_path})[/]")

def main():
    # argparse MUST be first — before any side effects
    parser = argparse.ArgumentParser(description="FlowGuard PoC — Code → Spec → Verify")
    parser.add_argument("files", nargs="*", help="Python agent files to analyse")
    parser.add_argument("--demo",         action="store_true", help="Run canonical webAgent + execAgent demo")
    parser.add_argument("--no-dashboard", action="store_true", help="Terminal output only")
    parser.add_argument("--skip-lean",    action="store_true", help="Skip lake build (faster, for demo without Lean installed)")
    parser.add_argument("--mode", choices=["ast", "llm", "both"], default=None, help="Extraction mode: ast (offline), llm (Gemini), both (merge). If omitted, asks interactively.")
    args = parser.parse_args()

    # Interactive mode selection if not passed as flag
    extraction_mode = args.mode
    if extraction_mode is None:
        console.print("\n[bold cyan]Extraction mode[/]")
        console.print("  [1] ast   — regex + filename heuristics (offline, fast)")
        console.print("  [2] llm   — Gemini 2.0 Flash (requires GEMINI_API_KEY)")
        console.print("  [3] both  — AST first, LLM refines, results merged (recommended)")
        choice = input("\n  Choose [1/2/3] (default 1): ").strip() or "1"
        extraction_mode = {"1": "ast", "2": "llm", "3": "both"}.get(choice, "ast")
        console.print(f"  → Using mode: [bold]{extraction_mode}[/]\n")

    files = args.files
    if args.demo:          files = DEMO_AGENTS
    if not files:
        parser.print_help()
        sys.exit(1)

    print_banner()

    # Lean build (skippable if Lean not installed locally)
    lean_checks  = []
    all_theorems = {}
    if not args.skip_lean:
        console.print("\n[dim]Running lake build on FlowGuard repo...[/]")
        build = run_lake_build()
        if build["success"]:
            console.print("[green]✓ lake build passed — Lean kernel verified all proofs[/]")
        else:
            console.print(f"[yellow]⚠ lake build: {build['errors'] or 'not found — run with --skip-lean to bypass'}[/]")
        lean_checks  = verify_demo_in_lean()
        print_lean_verification(lean_checks)
        all_theorems = get_all_theorems()
    else:
        console.print("[yellow]⚠ Skipping lake build (--skip-lean)[/]")
        all_theorems = get_all_theorems()   # still reads .lean files; no subprocess needed

    # Phase 1: Extract
    console.print("\n[dim]Extracting capability specs...[/]")
    specs = []
    for f in files:
        try:
            specs.append(extract_spec(f, mode=extraction_mode))
        except FileNotFoundError as e:
            console.print(f"[red]Error:[/] {e}")
            sys.exit(1)

    print_extraction(specs)

    # Phase 2 + 3: Verify
    console.print("\n[dim]Running FlowGuard verification...[/]")
    result = verify_pipeline(specs)

    print_individual_checks(result)
    print_composition_result(result)
    print_cedar_panel(result)
    print_ifc_panel(result)
    print_theorems(result, all_theorems)

    # Launch dashboard
    if not args.no_dashboard:
        launch_dashboard()

if __name__ == "__main__":
    main()