# FlowGuard

**Machine-checked proofs that safety does not compose in multi-agent AI systems.**

FlowGuard is a Lean 4 formalization of a fundamental and underappreciated problem in AI
safety: *an AI pipeline can be dangerous even when every agent inside it is individually
safe.* We prove this across six independent layers — capability hypergraphs, information-flow
control, a free monad model of agent programs, a unified safety certificate, Cedar
incompleteness, and a bridge between the operational and declarative models — and unify
them into a single compile-time safety certificate.

All ~100 theorems are fully kernel-checked. There are **zero `sorry`s**.

---

## The Problem — Explained Without Lean

Imagine you hire two contractors for your house.

- **Contractor A** has a key to the front door. Nothing else. Safe.
- **Contractor B** has access to your safe. Nothing else. Safe.

Now imagine they work together — and together, they can open your safe, copy its contents,
and leave through the front door. Suddenly the system is unsafe, even though each
individual contractor was vetted and trusted.

This is not a contrived example. It is the central problem in multi-agent AI security.

Modern AI assistants are increasingly built as **pipelines of specialised agents** — one
agent searches the web, another executes code, another reads a database, another sends
emails. Each agent is designed with a limited, audited set of capabilities. Safety reviews
happen per-agent. But when these agents are composed into a team:

- A `webSearch` agent + a `codeExec` agent → can together **exfiltrate data** to an
  external server, even if neither agent could do it alone.
- A medical pipeline where each data-sharing hop is individually approved → can create a
  transitive path where **secret patient records reach a public report**.

This property — that safety is **not preserved under composition** — is formally called
**non-compositionality**. It is known in the academic literature, but to our knowledge
this is the first machine-checked, compiler-verified proof of it in the context of AI
agent systems.

**FlowGuard provides those proofs.**

---

## Origin

This project was built during the **LeanLang for Verified Autonomy Hackathon**
(April 17–18 + online through May 1, 2026) at the
**Indian Institute of Science (IISc), Bangalore**.
Organized by **[Emergence India Labs](https://east.emergence.ai)** in collaboration with
IISc Bangalore. Sponsored by Emergence AI.

---

## What This Repository Contains

FlowGuard is a Lean 4 project. Lean is a **proof assistant** — a programming language
where you write not just code, but mathematical *proofs*, and the compiler checks every
proof for correctness with zero tolerance for errors. If the Lean compiler accepts a
theorem, it is guaranteed to be true. No human reviewer can introduce a mistake.

The project is structured in six layers, each building on the last.

```bash
git clone https://github.com/DevSoni31/FlowGuard.git
cd FlowGuard
lake build
# Expected: Build completed successfully (3304 jobs).
```

---

## Architecture

```text
┌─────────────────────────────────────────────────────────────────────────┐
│  CedarBridge.lean + CedarIncompleteness.lean                            │
│  Layers 5 & 6: Cedar is sound but incomplete for multi-agent pipelines  │
└────────────────────────────────┬────────────────────────────────────────┘
                                 │
              ┌──────────────────▼──────────────────────┐
              │  FlowCheck.lean                          │
              │  Layer 4: ValidPipeline +                │
              │  HopwiseValidPipeline unified cert.      │
              └──────────────┬───────────────┬───────────┘
                             │               │
          ┌──────────────────▼───┐   ┌───────▼──────────────────┐
          │  CapHypergraph.lean  │   │  InfoFlow.lean            │
          │  Layer 1: cap        │   │  Layer 2: IFC lattice,    │
          │  closure, fixed-     │   │  cascaded declassif.,     │
          │  point theory,       │   │  hopwise vs transitive    │
          │  universal non-      │   │  safety hierarchy         │
          │  compositionality    │   └──────────────────────────-┘
          └──────────┬───────────┘
                     │
          ┌──────────▼────────────────┐
          │  AgentProgram.lean        │
          │  Layer 3: Prog free monad │
          │  SafeProg, bridge to L1   │
          └───────────────────────────┘
```

---

## Layer 1 — Capability Hypergraphs (`CapHypergraph.lean`)

**The idea:** Agent capabilities are not just sets — they interact. Give one agent
`webSearch` and another `codeExec`, and the hyperedge `{webSearch, codeExec} → exfilData`
fires: the composed team now holds `exfilData`, which neither agent held alone.

We model this with a **hypergraph closure operator** — starting from the base capabilities
of a team, we repeatedly fire all applicable hyperedges until no new capabilities emerge.
The result is the *emergent capability set* of the pipeline. The full fixed-point theory
guarantees this process terminates and delivers the **tightest possible** safety boundary.

### Fixed-Point Theory

| Theorem | Mathematical Content |
|---|---|
| `capClosure_mono` | S ⊆ T → capClosure(S) ⊆ capClosure(T) |
| `capClosure_extensive` | S ⊆ capClosure(S) — base caps survive |
| `capClosure_is_fixpoint` | step(capClosure(S)) = capClosure(S) — it converges |
| `capClosure_is_least_fixpoint` | If S ⊆ T and step(T) ⊆ T, then capClosure(S) ⊆ T |

`capClosure_is_least_fixpoint` is the strongest property: `capClosure` is not merely
*a* closed superset — it is the *smallest possible* one. This is the mathematical
guarantee that FlowGuard's safety boundary is tight, not conservative.

### Non-Compositionality

| Theorem | Plain English |
|---|---|
| `webAgent_is_safe` | The web-search agent alone cannot exfiltrate data |
| `execAgent_is_safe` | The code-execution agent alone cannot exfiltrate data |
| `composedTeam_is_unsafe` | Together, `exfilData` emerges via hyperedge closure |
| `nonCompositionalityCounterexample` | **Headline:** both safe individually, unsafe together |
| `nonCompositionality_exists` | **∃-form:** there exist edges and agents where safety fails to compose |
| `nonCompositionality_universal` | **∀-form:** for ANY edges, ANY two agents fitting the structural premises, composition is unsafe |
| `coalition_nonCompositionality_universal` | **Coalition form:** for ANY agent list, ANY dangerous pair poisons the whole coalition |

`nonCompositionality_universal` is the research-paper-level result: it is not tied to any
specific agents. It holds for any hyperedge set and any two agents where neither holds all
premises alone, together they do, and the conclusion is forbidden for one.

### Safe Region Structure (Moore Family)

| Theorem | Plain English |
|---|---|
| `safeRegion_downward_closed` | A smaller base set is always at least as safe |
| `safeRegion_closed_under_intersection` | The intersection of two safe base sets is safe |
| `compose_forbidden_union_justified` | Union of forbidden sets is the correct semantics for composition |

---

## Layer 2 — Information-Flow Control (`InfoFlow.lean`)

**The idea:** Data carries a confidentiality label — `low`, `medium`, or `high`. A secure
system must never allow high-confidentiality data to reach a low-confidentiality output.
We check this not just for individual channels, but for the transitive composition of the
entire pipeline.

**The medical counterexample:** A hospital's diagnostic agent holds `High`-labelled patient
records. A summarisation step is locally approved (`High → Medium`). An anonymisation step
is locally approved (`Medium → Low`). The composed pipeline creates `High → Low`: secret
patient data reaches a public report. Each hop was approved; the system violates
noninterference.

### Core IFC Theorems

| Theorem | Plain English |
|---|---|
| `nonInterference_nonCompositional` | **Headline:** local approval ≠ global security |
| `localApproval_not_transitive` | **∃-form:** there exist labels where local approval fails to compose |
| `secureFlow_transitive` | The global lattice IS transitive — the flaw is in local policy |
| `insecure_flows_characterised` | **Complete characterisation:** exactly 3 downward flows are insecure |

### Parametric IFC Theorem

| Theorem | Plain English |
|---|---|
| `cascaded_declassification_parametric` | For ANY local policy, if it approves a two-hop chain with a net insecure flow, it is compositionally dangerous |
| `medical_hops_dangerous_for_any_policy` | Even a restrictive policy approving only the two medical hops is provably dangerous |

`cascaded_declassification_parametric` is the universal IFC result: it holds for any
policy function, not just the maximally permissive `locallyApproved`. The problem is
structural.

### Hopwise vs Transitive Safety

| Theorem | Plain English |
|---|---|
| `transitive_safety_misses_intermediate` | ∃ pipeline: `isTransitivelySafe = true` yet `isHopwiseSafe = false` |
| `hopwise_safe_not_implies_transitive_safe` | ∃ pipeline: `isHopwiseSafe = true` yet `isTransitivelySafe = false` |
| `isTransitivelySafe_only_checks_endpoints` | ∀ pipelines with secure src→dst endpoints pass the transitive check regardless of intermediate hops |
| `hopwise_is_necessary_for_intermediate_safety` | Only `isHopwiseSafe` can detect interior violations |

The two checks are **genuinely incomparable** — neither implies the other, proven by
witnesses in both directions. Both are required for a maximally certified pipeline.

---

## Layer 3 — Agent Programs as Free Monads (`AgentProgram.lean`)

**The idea:** Rather than reasoning only about what capabilities an agent *holds*, we also
reason about what programs an agent *runs*. An agent program is a tree of effects modelled
as a **free monad**, directly inspired by Prof. Gadgil's `FileM` in
[LeanLangur](https://github.com/siddhartha-gadgil/LeanLangur).

### Key Definitions and Theorems

| Name | What it is |
|---|---|
| `AgentEffect` | 5 primitive operations: webSearch, codeExec, readDB, sendEmail, exfilData |
| `Prog` | Free monad: pure value or effect followed by a continuation |
| `SafeProg` | Inductive safety predicate over program trees |
| `bindSafe` | If `x` is safe and every continuation `f a` is safe, then `x >>= f` is safe |
| `searchProg_safe` | A web-search-only program is safe for `webAgent` |
| `exfilProg_unsafe` | A search-then-exfiltrate program is **not** safe for `webAgent` |

### Bridge to Layer 1

| Theorem | Plain English |
|---|---|
| `safeProg_caps_in_base` | Every effect in a SafeProg-safe program uses only caps in `contract.base` |
| `safeProg_base_forbidden_disjoint` | Every used cap is in `base \ forbidden` |
| `safeProg_implies_capSafe_empty_edges` | **Adequacy:** SafeProg-safe + disjoint contract → `isCapSafe [] = true` |
| `safeProg_does_not_imply_capSafe` | **Independence:** SafeProg is a program-level check; `isCapSafe` is a contract-level check. Both are needed. |

---

## Layer 4 — The Unified Certificate (`FlowCheck.lean`)

**The idea:** All layers are unified into a single typeclass `ValidPipeline`. A pipeline
receives this certificate only if it simultaneously satisfies capability safety (Layer 1)
and transitive IFC (Layer 2). If it cannot, the Lean compiler rejects it. Safety becomes
a **compile-time guarantee**, not a runtime check.

### Core Certificate Theorems

| Theorem | Plain English |
|---|---|
| `validPipeline_iff` | **Complete characterisation:** `ValidPipeline P ↔ capSafe ∧ ifcSafe` |
| `flowguard_sound` | `ValidPipeline P` → both guarantees hold |
| `flowguard_complete` | Both guarantees hold → construct a `ValidPipeline` certificate |
| `validPipeline_reject_capUnsafe` | Any cap-unsafe agent → no certificate exists |
| `validPipeline_reject_ifcUnsafe` | Any downward net flow → no certificate exists |
| `trustedPipeline_valid` | A concrete pipeline **does** receive a full certificate |

### The Strongest Certificate — `HopwiseValidPipeline`

`ValidPipeline` enforces transitive IFC, which checks only the pipeline's two endpoints.
`HopwiseValidPipeline` extends it with a third obligation: **every individual hop** must
also respect the security lattice.

| Theorem | Plain English |
|---|---|
| `hopwiseValidPipeline_full_certificate` | Three-way certificate: cap safety + hopwise IFC + transitive IFC |
| `hopwiseValidPipeline_rejects_intermediate_violations` | Any intermediate hop violation → no certificate |
| `validPipeline_hierarchy` | `HopwiseValidPipeline → ValidPipeline`, not vice versa (witness provided) |

---

## Layers 5 & 6 — Cedar Incompleteness (`CedarBridge.lean` + `CedarIncompleteness.lean`)

**The idea:** Cedar is Amazon's production authorization language — formally verified, used
in AWS, and the current state of the art in deployed AI access control. Cedar is *sound*:
it correctly enforces what it is designed to enforce. FlowGuard proves Cedar is
*incomplete* for multi-agent pipelines: its request model has no concept of capability
emergence or transitive information flow. These are **structural gaps in Cedar's threat
model**, not bugs.

| Theorem | Plain English |
|---|---|
| `cedar_blind_to_capsets` | Two agents with the same name are Cedar-indistinguishable on any request — the blindness is enforced by type |
| `cedar_nonCompositionality_gap` | Cedar approves both agents; FlowGuard proves `exfilData ∈ capClosure(webAgent ∪ execAgent)` |
| `cedar_incomplete_universally` | **Universal form:** for any agents where composition is unsafe, Cedar cannot detect the emergent cap |
| `cedar_ifc_gap` | Cedar approves every hop in the medical pipeline; FlowGuard proves the transitive flow is unsafe |
| `cedar_is_incomplete` | **Master result:** Cedar is sound but incomplete — both gaps machine-checked simultaneously |
| `cedarAware_strictly_weaker` | Cedar approves the pipeline; FlowGuard rejects it — FlowGuard is strictly stronger |

---

## Why This Matters

Current AI safety tools — guardrails, red-teaming, constitutional AI — almost universally
evaluate agents **in isolation**. FlowGuard demonstrates, with machine-checked mathematical
proof, that this is insufficient.

- **AI governance frameworks** that certify individual models are incomplete without compositional guarantees.
- **Multi-agent orchestration platforms** (LangChain, AutoGen, CrewAI) need pipeline-level safety analysis, not just per-agent evaluation.
- **Production authorization languages** (Cedar, OPA, RBAC) have structural blind spots for emergent capabilities — FlowGuard proves this, not merely argues it.
- **Formal verification** of AI systems is tractable today — the proofs in this repository compile, are machine-checked, and can be extended.

---

## Quick Start

**Requirements:** Lean 4 and `elan`. The correct toolchain is pinned in `lean-toolchain`.

```bash
git clone https://github.com/DevSoni31/FlowGuard.git
cd FlowGuard
lake build
# Build completed successfully (3304 jobs).
```

```text
FlowGuard/
├── CapHypergraph.lean       # Layer 1: cap closure, fixed-point theory, universal non-compositionality
├── InfoFlow.lean            # Layer 2: IFC lattice, parametric cascaded declassification, hopwise safety
├── AgentProgram.lean        # Layer 3: Prog free monad, SafeProg, bridge to Layer 1
├── FlowCheck.lean           # Layer 4: ValidPipeline, HopwiseValidPipeline, iff characterisation
├── CedarBridge.lean         # Layer 5: Cedar policy definitions, incompleteness master theorem
├── CedarIncompleteness.lean # Layer 6: cedar_blind_to_capsets, universal Cedar incompleteness
└── Basic.lean               # Module entry point
```

---

## Theorem Index

| Theorem | File | What it proves |
|---|---|---|
| `nonCompositionalityCounterexample` | CapHypergraph | webAgent safe ∧ execAgent safe ∧ composition unsafe |
| `nonCompositionality_universal` | CapHypergraph | ∀ edges, agents satisfying structural premises → composition unsafe |
| `coalition_nonCompositionality_universal` | CapHypergraph | ∀ agent lists, any dangerous pair poisons the coalition |
| `capClosure_is_fixpoint` | CapHypergraph | step(capClosure(S)) = capClosure(S) |
| `capClosure_is_least_fixpoint` | CapHypergraph | capClosure is the smallest closed superset |
| `compose_forbidden_union_justified` | CapHypergraph | Union of forbidden sets is the correct composition semantics |
| `nonInterference_nonCompositional` | InfoFlow | All local hops approved ∧ transitive flow globally unsafe |
| `cascaded_declassification_parametric` | InfoFlow | ∀ policies approving a downward two-hop chain → compositionally dangerous |
| `isTransitivelySafe_only_checks_endpoints` | InfoFlow | ∀ good-endpoint pipelines pass transitive check regardless of middle |
| `safeProg_implies_capSafe_empty_edges` | AgentProgram | SafeProg-safe + disjoint contract → isCapSafe [] = true |
| `safeProg_does_not_imply_capSafe` | AgentProgram | SafeProg and isCapSafe are independent (correct separation of concerns) |
| `validPipeline_iff` | FlowCheck | ValidPipeline P ↔ capSafe ∧ ifcSafe |
| `hopwiseValidPipeline_full_certificate` | FlowCheck | Three-way certificate: cap + hopwise + transitive |
| `validPipeline_hierarchy` | FlowCheck | HopwiseValidPipeline → ValidPipeline, not vice versa |
| `cedar_blind_to_capsets` | CedarIncompleteness | Same-name agents are Cedar-indistinguishable on any request |
| `cedar_incomplete_universally` | CedarIncompleteness | ∀ agents where composition is unsafe, Cedar cannot detect it |
| `cedar_is_incomplete` | CedarBridge | Cedar is sound but incomplete — both gaps machine-checked |

---

## References

1. Spera, M. (2026). *Safety is Non-Compositional: A Formal Framework for Capability-Based AI Systems.*
   [arXiv:2603.15973](https://arxiv.org/abs/2603.15973)

2. Costa, et al. (2025). *Securing AI Agents with Information-Flow Control.*
   [arXiv:2505.23643](https://arxiv.org/abs/2505.23643)

3. Clarkson, M. R., & Schneider, F. B. (2010). *Hyperproperties.*
   [Journal of Computer Security, 18(6), 1157–1210](https://ecommons.cornell.edu/bitstream/1813/11660/4/hyperproperties-tr.pdf)

4. Gadgil, S. (2026). *LeanLangur — Language and formal verification experiments.*
   [github.com/siddhartha-gadgil/LeanLangur](https://github.com/siddhartha-gadgil/LeanLangur)

5. de Moura, L., & Ullrich, S. (2021). *The Lean 4 theorem prover and programming language.*
   [CADE 2021](https://lean-lang.org/papers/lean4.pdf)

6. Cutler, J. & others. (2024).
   *Cedar: A new language for expressive, fast, safe, and analyzable authorization.*
   [Amazon Science](https://www.amazon.science/publications/cedar-a-new-language-for-expressive-fast-safe-and-analyzable-authorization)

---

## Acknowledgements

**Emergence AI** — Hackathon sponsor  
**Emergence India Labs** — Event organizer and research direction  
**Indian Institute of Science (IISc), Bangalore** — Academic partner, hackathon co-design, tutorials, and mentorship

---

## Links

[Hackathon Page](https://east.emergence.ai/hackathon-april2026.html) ·
[Emergence India Labs](https://east.emergence.ai/) ·
[Emergence AI](https://www.emergence.ai/)

---

> "The question is not whether individual AI agents are safe.  
> The question is whether their composition is."