"""
verifier.py — Phase 2 & 3: Spec → Verify
Runs all FlowGuard checks. Returns a structured result dict
that both the terminal reporter and the browser dashboard consume.
"""
from hyperedges import (
    HYPEREDGE_LIBRARY, is_cap_safe, compose_list, get_fired_edges,
    cap_closure, is_transitively_safe, is_hopwise_safe,
    cedar_eval, cedar_team_eval, ALLOW, DENY
)

def verify_pipeline(specs: list) -> dict:
    """
    Full FlowGuard verification of a list of agent specs.
    Returns a result dict consumed by reporter.py and server.py.
    """
    edges  = HYPEREDGE_LIBRARY
    agents = [s["agent"] for s in specs]

    # ── Individual safety ────────────────────────────────────────────────────
    individual = []
    for s in specs:
        a    = s["agent"]
        safe = is_cap_safe(edges, a)
        em   = cap_closure(edges, a.base)
        individual.append({
            "name":      a.name,
            "base":      sorted(a.base),
            "forbidden": sorted(a.forbidden),
            "emergent":  sorted(em),
            "safe":      safe,
            "theorem":   "webAgent_is_safe / execAgent_is_safe (CapHypergraph.lean)",
            "method":    s["method"],
            "filepath":  s["filepath"],
        })

    # ── Composition ──────────────────────────────────────────────────────────
    composed       = compose_list(agents)
    composed_safe  = is_cap_safe(edges, composed)
    fired          = get_fired_edges(edges, composed)
    composed_em    = cap_closure(edges, composed.base)

    # ── Cedar comparison (mirrors cedar_nonCompositionality_gap) ─────────────
    all_cedar_pols = []
    for s in specs:
        all_cedar_pols.extend(s.get("cedar_policies", []))

    cedar_checks = []
    for cap in sorted(composed.forbidden):
        for s in specs:
            a = s["agent"]
            decision = cedar_team_eval(cap, all_cedar_pols)
            cedar_checks.append({
                "principal": a.name,
                "action":    cap,
                "decision":  decision,
            })
    cedar_denies_all = all(c["decision"] == DENY for c in cedar_checks if c["action"] in composed.forbidden)
    # Cedar blind spot: Cedar says DENY for all forbidden, but FlowGuard finds UNSAFE
    cedar_blind = cedar_denies_all and (not composed_safe)

    # ── IFC pipeline check ───────────────────────────────────────────────────
    all_channels = []
    for s in specs:
        all_channels.extend(s.get("pipeline_channels", []))
    ifc_transitive = is_transitively_safe(all_channels) if all_channels else None
    ifc_hopwise    = is_hopwise_safe(all_channels)       if all_channels else None

    # ── Theorem citations ────────────────────────────────────────────────────
    theorems_cited = []
    if not composed_safe:
        theorems_cited.append({
            "name": "nonCompositionality_universal",
            "file": "CapHypergraph.lean",
            "statement": "∀ edges a b, isCapSafe edges a = true → isCapSafe edges b = true → (∃ e ∈ edges, …) → isCapSafe edges (compose a b) = false",
            "english": "For any agents and hyperedges satisfying the structural premises, individual safety does not survive composition.",
        })
    if cedar_blind:
        theorems_cited.append({
            "name": "cedar_nonCompositionality_gap",
            "file": "CedarBridge.lean",
            "statement": "cedarEval teamPolicy {exfilData} = deny ∧ isCapSafe demoEdges (compose webAgent execAgent) = false",
            "english": "Cedar denies exfilData for every individual request, yet FlowGuard proves the composed team can exfiltrate.",
        })
    if all_channels and not ifc_transitive:
        theorems_cited.append({
            "name": "nonInterference_nonCompositional",
            "file": "InfoFlow.lean",
            "statement": "allLocallyApproved medicalPipeline = true ∧ isTransitivelySafe medicalPipeline = false",
            "english": "Every local channel is approved, yet the composed pipeline violates the global security lattice.",
        })

    return {
        "individual":       individual,
        "composed": {
            "name":      composed.name,
            "base":      sorted(composed.base),
            "forbidden": sorted(composed.forbidden),
            "emergent":  sorted(composed_em),
            "safe":      composed_safe,
        },
        "fired_edges":      [{"label": e.label, "premises": sorted(e.premises), "conclusion": e.conclusion} for e in fired],
        "cedar": {
            "checks":       cedar_checks,
            "denies_all":   cedar_denies_all,
            "blind_spot":   cedar_blind,
            "explanation":  "Cedar evaluates each (principal, action) request in isolation. It cannot detect capability emergence from agent composition. This is not a Cedar bug — it is a structural limitation of the per-request policy paradigm. See: CedarBridge.lean, theorem cedar_nonCompositionality_gap.",
        },
        "ifc": {
            "channels":         all_channels,
            "transitive_safe":  ifc_transitive,
            "hopwise_safe":     ifc_hopwise,
        },
        "theorems_cited": theorems_cited,
        "verdict": "SAFE" if composed_safe else "UNSAFE",
    }