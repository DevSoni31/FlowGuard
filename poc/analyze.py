"""
analyze.py — FlowGuard PoC main entry point.
Usage:
  python analyze.py agent1.py agent2.py [agent3.py ...]
  python analyze.py --demo          # runs the canonical webAgent + execAgent demo
  python analyze.py --medical-demo  # runs the medical pipeline IFC demo
"""

from lean_bridge import run_lake_build, verify_demo_in_lean, get_all_theorems
import sys, json, os, argparse, threading, webbrowser, time
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
MEDICAL_AGENTS = ["sample_agents/medical_pipeline.py"]

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

def print_theorems(result: dict):
    if not result["theorems_cited"]:
        return
    console.rule("[bold cyan]Theorems Cited (FlowGuard.lean)[/]")
    for t in result["theorems_cited"]:
        console.print(f"\n  [bold cyan]{t['name']}[/]  [dim]{t['file']}[/]")
        console.print(f"  [dim italic]{t['statement']}[/]")
        console.print(f"  → {t['english']}")

def launch_dashboard(result: dict, specs: list):
    """Write result.json and open the browser dashboard."""
    output = {
        "result": result,
        "specs":  [{"name": s["agent"].name, "filepath": s["filepath"],
                    "method": s["method"], "description": s["description"]} for s in specs]
    }
    Path("result.json").write_text(json.dumps(output, indent=2))

    # Start Flask server
    import server as srv
    t = threading.Thread(target=srv.run, daemon=True)
    t.start()
    time.sleep(1.2)
    webbrowser.open("http://localhost:5050")
    console.print("\n[bold cyan]Dashboard opened at http://localhost:5050[/]")
    console.print("[dim]Press Ctrl+C to exit.[/]")
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        pass

def main():
    console.print("\n[dim]Running lake build on FlowGuard repo...[/]")
    build = run_lake_build()
    if build["success"]:
        console.print("[green]✓ lake build passed — Lean kernel verified all proofs[/]")
    else:
        console.print(f"[yellow]⚠ lake build errors: {build['errors']}[/]")

    lean_checks = verify_demo_in_lean()   # real Lean output for the dashboard
    all_theorems = get_all_theorems()     # real theorem list from your .lean files
    parser = argparse.ArgumentParser(description="FlowGuard PoC — Code → Spec → Verify")
    parser.add_argument("files", nargs="*", help="Python agent files to analyse")
    parser.add_argument("--demo",         action="store_true", help="Run canonical webAgent + execAgent demo")
    parser.add_argument("--medical-demo", action="store_true", help="Run medical pipeline IFC demo")
    parser.add_argument("--no-dashboard", action="store_true", help="Terminal output only")
    args = parser.parse_args()

    files = args.files
    if args.demo:          files = DEMO_AGENTS
    if args.medical_demo:  files = MEDICAL_AGENTS
    if not files:
        parser.print_help()
        sys.exit(1)

    print_banner()

    # Phase 1: Extract
    console.print("\n[dim]Extracting capability specs...[/]")
    specs = []
    for f in files:
        try:
            specs.append(extract_spec(f))
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
    print_theorems(result)

    # Launch dashboard
    if not args.no_dashboard:
        launch_dashboard(result, specs)

if __name__ == "__main__":
    main()