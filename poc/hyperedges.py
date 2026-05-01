"""
hyperedges.py
Python mirror of:
  FlowGuard.CapHypergraph  — HyperEdge, Agent, step, capClosure, compose
  FlowGuard.InfoFlow       — secureFlow, isTransitivelySafe, isHopwiseSafe
  FlowGuard.CedarBridge    — cedarEval, cedar_team_eval

The algorithm (step / capClosure) is identical to the Lean definitions.
The Lean kernel separately verifies all proofs; this file is the fast
runtime engine used to check new Python agents without a full Lean build.
"""
from dataclasses import dataclass
from typing import FrozenSet, List

# Matches Fintype.card Cap = 13 in CapHypergraph.lean
ALL_CAPS = {
    "webSearch", "codeExec", "readDB", "sendEmail", "exfilData",
    "fileRead", "networkAccess", "shellExec", "databaseQuery",
    "emailSend", "privEsc", "remoteExec", "dataLeak"
}

@dataclass(frozen=True)
class HyperEdge:
    """Mirrors `structure HyperEdge` in CapHypergraph.lean"""
    premises:   FrozenSet[str]
    conclusion: str
    label:      str = ""
    def __repr__(self):
        return f"{{{', '.join(sorted(self.premises))}}} → {self.conclusion}"

@dataclass
class Agent:
    """Mirrors `structure Agent` in CapHypergraph.lean"""
    name:      str
    base:      FrozenSet[str]
    forbidden: FrozenSet[str]

# ── Core algorithm — mirrors CapHypergraph.lean exactly ───────────────────────

def step(edges: List[HyperEdge], S: FrozenSet[str]) -> FrozenSet[str]:
    """Mirrors `def step` — one saturation pass."""
    acc = set(S)
    for e in edges:
        if e.premises.issubset(acc):
            acc.add(e.conclusion)
    return frozenset(acc)

def closure_aux(n: int, edges: List[HyperEdge], S: FrozenSet[str]) -> FrozenSet[str]:
    """Mirrors `def closureAux` — iterate step n times."""
    if n == 0:
        return S
    return closure_aux(n - 1, edges, step(edges, S))

def cap_closure(edges: List[HyperEdge], S: FrozenSet[str]) -> FrozenSet[str]:
    """Mirrors `def capClosure` — iterate |Cap| times.
    Termination guaranteed by capClosure_is_fixpoint (CapHypergraph.lean)."""
    return closure_aux(len(ALL_CAPS), edges, S)

def emergent(edges: List[HyperEdge], agent: Agent) -> FrozenSet[str]:
    return cap_closure(edges, agent.base)

def is_cap_safe(edges: List[HyperEdge], agent: Agent) -> bool:
    """Mirrors `def isCapSafe` — True iff no forbidden cap is reachable."""
    return len(emergent(edges, agent) & agent.forbidden) == 0

def compose(a: Agent, b: Agent) -> Agent:
    """Mirrors `def compose` in CapHypergraph.lean."""
    return Agent(
        f"{a.name}+{b.name}",
        frozenset(a.base | b.base),
        frozenset(a.forbidden | b.forbidden)
    )

def compose_list(agents: List[Agent]) -> Agent:
    """Mirrors `def composeList`."""
    acc = Agent("empty", frozenset(), frozenset())
    for a in agents:
        acc = compose(acc, a)
    return acc

def get_fired_edges(edges: List[HyperEdge], agent: Agent) -> List[HyperEdge]:
    """Returns edges that fire (i.e. cause new emergent caps) for this agent."""
    closure = cap_closure(edges, agent.base)
    return [e for e in edges
            if e.premises.issubset(closure) and e.conclusion not in agent.base]

# ── Hyperedge library — extends demoEdges from CapHypergraph.lean ─────────────
HYPEREDGE_LIBRARY = [
    HyperEdge(frozenset({"webSearch", "codeExec"}),     "exfilData",  "webSearch ∧ codeExec → exfilData"),
    HyperEdge(frozenset({"fileRead", "networkAccess"}),  "exfilData",  "fileRead ∧ networkAccess → exfilData"),
    HyperEdge(frozenset({"shellExec", "databaseQuery"}), "privEsc",    "shellExec ∧ databaseQuery → privEsc"),
    HyperEdge(frozenset({"emailSend", "readDB"}),        "dataLeak",   "emailSend ∧ readDB → dataLeak"),
    HyperEdge(frozenset({"codeExec", "networkAccess"}),  "remoteExec", "codeExec ∧ networkAccess → remoteExec"),
]

# ── Cedar simulation — mirrors CedarBridge.lean ───────────────────────────────
ALLOW, DENY = "allow", "deny"

def cedar_eval(principal: str, action: str, policies: list) -> str:
    """Mirrors `def cedarEval` — per-request evaluation."""
    for pol in policies:
        if pol.get("principal") == principal and pol.get("action") == action:
            return ALLOW
    return DENY

def cedar_team_eval(action: str, all_policies: list) -> str:
    """Mirrors `def teamPolicy` — union policy over all agents."""
    for pol in all_policies:
        if pol.get("action") == action:
            return ALLOW
    return DENY

# ── IFC — mirrors InfoFlow.lean ───────────────────────────────────────────────
LABEL_RANK = {"low": 0, "medium": 1, "high": 2}

def secure_flow(src: str, dst: str) -> bool:
    """Mirrors `def secureFlow` — src ≤ dst in the security lattice."""
    return LABEL_RANK.get(src, 0) <= LABEL_RANK.get(dst, 0)

def is_transitively_safe(channels: list) -> bool:
    """Mirrors `def isTransitivelySafe` — endpoint-only check."""
    if not channels:
        return True
    return secure_flow(channels[0]["src"], channels[-1]["dst"])

def is_hopwise_safe(channels: list) -> bool:
    """Mirrors `def isHopwiseSafe` — every hop must satisfy secureFlow."""
    return all(secure_flow(ch["src"], ch["dst"]) for ch in channels)