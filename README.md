# FlowGuard

**Machine-checked proofs that safety does not compose in multi-agent AI systems.**

FlowGuard is a Lean 4 formalization of a fundamental and underappreciated problem in AI
safety: *an AI pipeline can be dangerous even when every agent inside it is individually
safe.* We prove this in three independent layers — capability hypergraphs, information-flow
control, and a free monad model of agent programs — and unify them into a single
compile-time safety certificate.

> Built for the **LeanLangur Hackathon 2025** at IISc Bangalore,
> supervised by [Prof. Siddhartha Gadgil](https://math.iisc.ac.in/~gadgil/).

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
**non-compositionality**. It is known in the academic literature, but to date there was no
machine-checked, compiler-verified proof of it in the context of AI agent systems.

**FlowGuard provides those proofs.**

---

## What This Repository Contains

FlowGuard is a Lean 4 project. Lean is a **proof assistant** — a programming language
where you write not just code, but mathematical *proofs*, and the compiler checks every
proof for correctness with zero tolerance for errors. If the Lean compiler accepts a
theorem, it is guaranteed to be true. No human reviewer can introduce a mistake.

The project is structured in four layers, each building on the last.

---

## Architecture

```text
┌─────────────────────────────────────────────────────────────┐
│ FlowCheck.lean │
│ ValidPipeline — the unified safety certificate │
│ Requires BOTH Layer 1 and Layer 2 to be satisfied │
└────────────────────────┬──────────────────┬─────────────────┘
│ │
┌──────────────▼──────┐ ┌────────▼──────────────┐
│ CapHypergraph.lean │ │ InfoFlow.lean │
│ Layer 1: Capability │ │ Layer 2: Information │
│ Emergence via │ │ Flow Control and │
│ Hyperedge Closure │ │ Transitive Safety │
└──────────────┬───────┘ └────────┬──────────────┘
│ │
└─────────┬─────────┘
│
┌──────────────▼──────────────┐
│ AgentProgram.lean │
│ Layer 3: Free Monad Model │
│ Programs as proof objects │
└──────────────────────────────┘
```


---

## Layer 1 — Capability Hypergraphs (`CapHypergraph.lean`)

**The idea:** Agent capabilities are not just sets — they interact. Give one agent
`webSearch` and another `codeExec` and the hyperedge `webSearch ∧ codeExec → exfilData`
fires: the composed team now holds the `exfilData` capability that neither agent held alone.

We model this with a **hypergraph closure operator** — starting from the base capabilities
of a team, we repeatedly fire all applicable hyperedges until no new capabilities emerge.
The result is the *emergent capability set* of the pipeline.

**Key theorems:**

| Theorem | Plain English |
|---|---|
| `webAgent_is_safe` | The web-search agent alone cannot exfiltrate data |
| `execAgent_is_safe` | The code-execution agent alone cannot exfiltrate data |
| `composedTeam_is_unsafe` | Together, they can — the `exfilData` capability emerges |
| `nonCompositionalityCounterexample` | **Headline:** both safe individually, unsafe together |

**Formalises:** Spera, M. (2026). *Hypergraph-based capability modelling for AI agent
safety.* arXiv:2603.15973

---

## Layer 2 — Information-Flow Control (`InfoFlow.lean`)

**The idea:** Data carries a confidentiality label — `low`, `medium`, or `high`. A secure
system must never allow high-confidentiality data to reach a low-confidentiality output.
We check this not just for individual channels, but for the **transitive composition** of
the entire pipeline.

The medical counterexample: a hospital's diagnostic agent holds `High`-labelled patient
records. A summarisation step is locally approved (`High → Medium`). An anonymisation step
is locally approved (`Medium → Low`). But the composed pipeline creates a path
`High → Low`: secret patient data reaches a public report.

Each individual hop was approved. The system as a whole violates noninterference.

**Key theorems:**

| Theorem | Plain English |
|---|---|
| `diagnosticChannel_locallyApproved` | The H→M hop is approved by its local policy |
| `summaryChannel_locallyApproved` | The M→L hop is approved by its local policy |
| `medicalPipeline_allLocallyApproved` | Every hop passes its own policy check |
| `medicalPipeline_globallyUnsafe` | The transitive flow H→L violates noninterference |
| `nonInterference_nonCompositional` | **Headline:** local approval ≠ global security |
| `safePipelineIFC_fullyVerified` | A genuinely safe pipeline (Low→High) is certified |

**Formalises:** Anon. (2025). *Compositional information-flow security for LLM pipelines.*
arXiv:2505.23643 §4; Clarkson & Schneider (2010). *Hyperproperties.*

---

## Layer 3 — Agent Programs as Free Monads (`AgentProgram.lean`)

**The idea:** Rather than reasoning about *what capabilities an agent holds*, we reason
about *what programs an agent runs*. An agent program is a tree of effects — web searches,
code executions, database reads — modelled as a **free monad**.

This architecture is directly inspired by Prof. Gadgil's `FileM` in
[LeanLangur](https://github.com/siddhartha-gadgil/LeanLangur). The `SafeProg` predicate
is an inductive proposition over program trees: a program is safe if every effect it
performs is permitted by the agent's capability contract, and this property is preserved
under sequential composition.

**Key definitions and theorems:**

| Name | What it is |
|---|---|
| `AgentEffect` | The 5 primitive operations: webSearch, codeExec, readDB, sendEmail, exfilData |
| `Prog` | Free monad: a program is either a pure value or an effect followed by a continuation |
| `SafeProg` | Inductive safety predicate over program trees |
| `bindSafe` | **Composition theorem:** if `x` is safe and every continuation `f a` is safe, then `x >>= f` is safe |
| `searchProg_safe` | A web-search-only program is safe for `webAgent` |
| `exfilProg_unsafe` | A search-then-exfiltrate program is **not** safe for `webAgent` |

The `bindSafe` theorem is the monad-level statement of the same non-compositionality
insight: composition is safe *only when both halves are independently verified*. Safety
does not transfer automatically.

---

## Layer 4 — The Unified Certificate (`FlowCheck.lean`)

**The idea:** All three layers are unified into a single typeclass `ValidPipeline`. A
pipeline only receives this certificate if it simultaneously satisfies:

1. **Capability safety** — no emergent capability reaches any forbidden set (Layer 1)
2. **Transitive IFC** — no high-confidentiality data reaches a low-confidentiality output (Layer 2)

If a pipeline cannot synthesise a `ValidPipeline` instance, the Lean compiler rejects it.
Safety becomes a **compile-time guarantee**, not a runtime check.

**Key theorems:**

| Theorem | Plain English |
|---|---|
| `unsafePipelineCap_not_valid` | The capability-unsafe pipeline cannot be certified |
| `unsafePipelineIFC_not_valid` | The medical pipeline cannot be certified |
| `trustedPipeline_valid` | A concrete pipeline **does** receive a full certificate |
| `flowguard_sound` | **Master theorem:** `ValidPipeline P` implies both guarantees hold |
| `trustedPipeline_certified` | The trusted pipeline satisfies both guarantees, machine-checked |

---

## Why This Matters

Current AI safety tools — guardrails, red-teaming, constitutional AI — almost universally
evaluate agents **in isolation**. FlowGuard demonstrates, with machine-checked mathematical
proof, that this is insufficient. A system can pass every individual safety check and still
be dangerous at the pipeline level.

The implications are immediate:

- **AI governance frameworks** that certify individual models are incomplete without
  compositional guarantees.
- **Multi-agent orchestration platforms** (LangChain, AutoGen, CrewAI) need pipeline-level
  safety analysis, not just per-agent evaluation.
- **Formal verification** of AI systems is tractable today — the proofs in this repository
  are not theoretical. They compile, they are machine-checked, and they can be extended.

FlowGuard is a proof of concept that the formal methods community and the AI safety
community have a shared vocabulary, and Lean 4 + Mathlib is the right language to speak it.

---

## Quick Start

**Requirements:** Lean 4, `elan`, and `lake` (the Lean build tool).
If you have [elan](https://github.com/leanprover/elan) installed, the correct Lean version
is pinned in `lean-toolchain` and will be fetched automatically.

```bash
# Clone the repository
git clone https://github.com/DevSoni31/FlowGuard.git
cd FlowGuard

# Build all proofs (downloads Mathlib on first run — may take a few minutes)
lake build

# Expected output:
# Build completed successfully (3304 jobs).
```

All proofs are in `FlowGuard/`. There are no `sorry`s — every theorem is fully proved.

---

## File Structure

```text
FlowGuard/
├── CapHypergraph.lean # Layer 1: capability hypergraph closure + counterexample
├── InfoFlow.lean # Layer 2: security labels, IFC, cascaded declassification
├── AgentProgram.lean # Layer 3: free monad model of agent programs
├── FlowCheck.lean # Layer 4: ValidPipeline unified certificate
└── Basic.lean # Module entry point
```


---

## References

1. Spera, M. (2026). *Hypergraph-based capability modelling for multi-agent AI safety.*
   [arXiv:2603.15973](https://arxiv.org/abs/2603.15973)

2. Anon. (2025). *Compositional information-flow security for LLM agent pipelines.*
   [arXiv:2505.23643](https://arxiv.org/abs/2505.23643)

3. Clarkson, M. R., & Schneider, F. B. (2010). *Hyperproperties.*
   Journal of Computer Security, 18(6), 1157–1210.

4. Gadgil, S. (2025). *LeanLangur — Language and formal verification experiments.*
   [github.com/siddhartha-gadgil/LeanLangur](https://github.com/siddhartha-gadgil/LeanLangur)

5. de Moura, L., & Ullrich, S. (2021). *The Lean 4 theorem prover and programming language.*
   CADE 2021.

---

## Acknowledgements

This project was developed during the **LeanLangur Hackathon** organised by
Prof. Siddhartha Gadgil at the Indian Institute of Science, Bangalore.
The architecture of `AgentProgram.lean` is directly inspired by `FileM.lean` in
[LeanLangur](https://github.com/siddhartha-gadgil/LeanLangur).

---

*"The question is not whether individual AI agents are safe.
The question is whether their composition is."*