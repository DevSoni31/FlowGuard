# FlowGuard

**Machine-checked proofs that safety does not compose in multi-agent AI systems.**

FlowGuard is a Lean 4 formalization of a fundamental and underappreciated problem in AI
safety: *an AI pipeline can be dangerous even when every agent inside it is individually
safe.* We prove this across six layers — capability hypergraphs, information-flow control,
a free monad model of agent programs, a unified safety certificate, Cedar incompleteness,
and a structural impossibility result — and unify them into a single compile-time safety
certificate verified by the Lean kernel.

Alongside the proofs, FlowGuard ships a Python proof-of-concept pipeline that reads real
agent source files, infers capability specifications dynamically (either from AST analysis
or via an LLM), runs the same hyperedge-closure and IFC checks implemented in the Lean
proofs, and then cites the exact theorem covering each finding — reading the theorem text
live from the compiled `.lean` files, not from any hardcoded strings.

All theorems are fully kernel-checked. There are **zero `sorry`s**.

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


## Demo

A full walkthrough of the FlowGuard PoC pipeline — capability extraction, hyperedge
closure, Cedar comparison, and live Lean theorem citation — is available here:

[![FlowGuard PoC Demo](https://img.youtube.com/vi/YOUR_VIDEO_ID/maxresdefault.jpg)](https://youtu.be/PLACEHOLDER)

The video covers:
- Cloning the repo and running `lake build` (time-lapsed)
- Running `python analyze.py --demo --no-dashboard --mode ast --skip-lean`
- The three-phase terminal output: extraction → individual checks → composition verdict
- The Cedar blind-spot panel and its connection to `cedar_nonCompositionality_gap`
- Live theorem citation: statement text read directly from `CapHypergraph.lean`
- Brief walkthrough of the `--medical-demo` path and the `isTransitivelySafe` vs
   `isHopwiseSafe` distinction

> The video is unlisted on YouTube — accessible via the link above only.
When you have the YouTube link, simply swap https://youtu.be/PLACEHOLDER with the real URL and replace YOUR_VIDEO_ID in the thumbnail link. Everything else stays identical.

If you want a plain-text fallback link, keep this format nearby:

```text
▶ FlowGuard PoC Demo: https://youtu.be/YOUR_VIDEO_ID
```

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

### Lean Proof Layers

```text
┌────────────────────────────────────────────────────────────────────────────┐
│  CedarIncompleteness.lean  (Layer 6)                                       │
│  Structural impossibility: no Cedar policy can be complete for pipelines   │
│  Key: cedar_blind_to_capsets, cedar_incomplete_universally,                │
│       cedar_capability_separation, joint_closure_strictly_larger           │
└───────────────────────────┬────────────────────────────────────────────────┘
                                          │ imports
┌───────────────────────────▼────────────────────────────────────────────────┐
│  CedarBridge.lean  (Layer 5)                                               │
│  Concrete counterexample: Cedar denies ∧ FlowGuard detects emergence       │
│  Key: cedar_nonCompositionality_gap, cedar_ifc_gap, cedar_is_incomplete,   │
│       cedarAware_strictly_weaker                                            │
└───────────────────────────┬────────────────────────────────────────────────┘
                                          │ imports
┌───────────────────────────▼────────────────────────────────────────────────┐
│  FlowCheck.lean  (Layer 4)                                                 │
│  Unified certificate: ValidPipeline ↔ capSafe ∧ ifcSafe (biconditional)   │
│  Key: validPipeline_iff, flowguard_sound, flowguard_complete,              │
│       hopwiseValidPipeline_full_certificate, validPipeline_hierarchy       │
└────────────────┬──────────────────────────────────────┬────────────────────┘
                         │ imports                               │ imports
┌────────────────▼───────────────────┐   ┌──────────────▼────────────────────┐
│  CapHypergraph.lean  (Layer 1)     │   │  InfoFlow.lean  (Layer 2)          │
│  Hyperedge closure, fixed-point    │   │  IFC lattice, cascaded declassif., │
│  theory, universal non-            │   │  hopwise vs transitive safety      │
│  compositionality, safe-region     │   │  hierarchy, parametric IFC theorem │
│  Moore family structure            │   └───────────────────────────────────-┘
└────────────────────────────────────┘
               ▲
               │ bridge: safeProg_implies_capSafe_empty_edges
┌─────────┴──────────────────────────┐
│  AgentProgram.lean  (Layer 3)      │
│  Prog free monad, SafeProg,        │
│  program-level ↔ contract-level    │
│  separation of concerns            │
└────────────────────────────────────┘
```

### Python PoC Pipeline

```text
   agent1.py, agent2.py, ...
            │
            ▼
   ┌─────────────────────────────────────────────────────────────────────┐
   │  extractor.py                                                        │
   │  Mode: ast  → Python AST walk, regex, filename heuristics           │
   │  Mode: llm  → Gemini 2.0 Flash semantic inference                   │
   │  Mode: both → AST first; LLM refines with AST as prior              │
   │  Output: AgentSpec {name, base: Set[Cap], forbidden: Set[Cap],      │
   │          data_label: Label, pipeline_channels: List[Channel]}       │
   └──────────────────────────┬──────────────────────────────────────────┘
                                           │
                                           ▼
   ┌─────────────────────────────────────────────────────────────────────┐
   │  verifier.py + hyperedges.py                                        │
   │  · isCapSafe: per-agent check (mirrors CapHypergraph.isCapSafe)    │
   │  · cap_closure: fixed-point iteration (mirrors capClosure)          │
   │  · is_transitively_safe / is_hopwise_safe (mirrors InfoFlow)        │
   │  · cedar_team_eval: Cedar simulation (mirrors CedarBridge)          │
   │  Output: full result dict — verdict, fired edges, IFC flags,        │
   │          Cedar comparison, theorem citations                         │
   └──────────────────────────┬──────────────────────────────────────────┘
                                           │
                                           ▼
   ┌─────────────────────────────────────────────────────────────────────┐
   │  lean_bridge.py                                                     │
   │  · run_lake_build(): invokes `lake build`, streams output           │
   │  · verify_demo_in_lean(): evaluates #eval / #check in Lean kernel   │
   │  · extract_theorems(): regex-parses *.lean → theorem name +         │
   │    statement (live, not hardcoded)                                  │
   │  · get_all_theorems(): indexes all 6 files at startup               │
   └──────────────────────────┬──────────────────────────────────────────┘
                                           │
                                           ▼
   ┌─────────────────────────────────────────────────────────────────────┐
   │  analyze.py                                                         │
   │  Terminal reporter — Rich panels, three-phase output, theorem       │
   │  citations with live statement text read from compiled .lean files  │
   │  Flags: --demo, --medical-demo, --mode [ast|llm|both],             │
   │         --skip-lean, --no-dashboard                                 │
   └─────────────────────────────────────────────────────────────────────┘
```

---

## Quick Start

### Prerequisites

Two things need to be installed before anything else.

**Lean 4 + elan** - Install from the [official Lean setup page](https://lean-lang.org/lean4/doc/setup.html)
following the instructions for your operating system. `elan` (the Lean version manager) is
installed alongside Lean and handles toolchain management automatically. The correct Lean
toolchain for this project is pinned in `lean-toolchain` at the repo root - `elan` will
read this file and switch to the right version without any manual intervention.

**Python 3.11+** - Standard installation from [python.org](https://python.org). No special
package manager is needed beyond the standard `venv` module that ships with Python.

---

### Step 1 - Clone the repository and fetch the Lean cache

```bash
git clone https://github.com/DevSoni31/FlowGuard.git
cd FlowGuard
```

Before building, fetch the pre-compiled Mathlib cache. This is a one-time step that
downloads already-compiled proof objects from the Lean cache server, avoiding a full
Mathlib recompile from source (which would take several hours):

```bash
lean exe cache get
```

> ⏱️ **Time estimate:** approximately **30 minutes** on the first run, depending on your
> network. On subsequent runs, the cache is already present and this step is instant.
> If you skip this step, `lake build` will attempt to rebuild Mathlib from source and
> will take considerably longer.

---

### Step 2 - Build the Lean proofs

```bash
lake build
```

This compiles all six `.lean` files through the Lean 4 kernel. The kernel does not merely
type-check - it reconstructs and verifies the full mathematical derivation of every
theorem. If it completes without errors, every proof in the repository is mathematically
guaranteed to be correct.

**Expected output:**
Build completed successfully (3304 jobs).

> ⏱️ **Time estimate:** approximately **25 minutes** on the first run. On subsequent runs
> with no `.lean` file changes, all 3304 jobs are cached and the build completes in about 5-10 minutes.

> ⚠️ This step **must** complete successfully before running the PoC. The Python pipeline
> sends live queries to the Lean kernel at runtime and resolves theorem statements directly
> from the compiled `.lean` files. If the build has not run, those queries will fail.

---

### Step 3 - Set up the Python environment

The PoC lives in the `poc/` subdirectory and has its own isolated Python environment.

```bash
cd poc
python -m venv .venv
```

Activate the environment:

```powershell
# Windows - run this once to allow script execution, then activate
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
.venv\Scripts\activate
```

```bash
# macOS / Linux
source .venv/bin/activate
```

Install dependencies:

```bash
pip install -r requirements.txt
```

The `requirements.txt` contains: `rich`, `google-genai`, `python-dotenv`, `requests`.
These are all standard, well-maintained packages and install in under a minute.

---

### Step 4 - Run the PoC pipeline

With the virtual environment active and the Lean build complete, run:

```bash
python analyze.py --demo --mode ast
```

**What each flag does:**

| Flag | Purpose |
|---|---|
| `--demo` | Runs the canonical capability-emergence scenario: `web_search_agent.py` + `code_exec_agent.py` |
| `--mode ast` | Uses the AST (Abstract Syntax Tree) extractor - reads agent source code directly, requires no API key, runs fully offline |

The pipeline will work through three phases: capability extraction from the agent source
files, individual safety checks per agent, and finally composition analysis with hyperedge
closure. At the end, it cites the exact Lean theorem covering each finding, with the
theorem statement read live from the compiled `.lean` files - not hardcoded.

> ⏱️ **Time estimate:** approximately **30 minutes** for the full run. The bulk of this
> time is the live Lean kernel queries during verification.

**Expected final output:**
COMPOSITION RESULT - UNSAFE
Emergent capability detected:
webSearch ∧ codeExec → exfilData
codeExec ∧ networkAccess → remoteExec
Theorem cited: nonCompositionality_universal (CapHypergraph.lean)

Once the pipeline finishes, the demo page (`flowguard-page.html`) will open automatically
in your default browser - no server required. It presents the full FlowGuard story
interactively: the problem, the proofs, the pipeline walkthrough, Cedar's structural blind
spot, and the final verdict.

---

### Optional - LLM extraction mode

`--mode ast` is the recommended path for replication because it requires no external
credentials and runs entirely offline. If you have a Gemini API key available, the LLM
extraction mode provides richer semantic capability inference:

1. Copy `.env.example` to `.env` at the repo root and add your key:
   GEMINI_API_KEY=your_key_here

2. Pass `--mode llm` instead:
```bash
python analyze.py --demo --mode llm
```

Or use `--mode both`, which runs AST extraction first and passes those results to
Gemini as a prior - this generally produces the most accurate capability spec:
```bash
python analyze.py --demo --mode both
```

The `--mode` flag is the only change required. Everything else - the Lean queries,
hyperedge closure, theorem citations, and the dashboard - works identically across all
three modes.

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

The safe-region theorems establish that the set of all safe agent base-sets forms a
**Moore family** (closed under intersection, downward-closed). This is a structural result
independent of any specific hyperedge configuration: no matter what capabilities exist,
the safe region always has this algebraic shape. This means that safety can in principle
be characterised by its boundary — the set of maximal safe base-sets — and this boundary
is unique and computable.

`coalition_nonCompositionality_universal` extends the pairwise result to **any finite
coalition**: if any dangerous pair exists within a list of agents, the entire coalition
is unsafe. This is the theorem the PoC invokes when more than two agents are passed on
the command line.

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

The incomparability of `isTransitivelySafe` and `isHopwiseSafe` is one of the most
practically significant results in the project. It means:

- A pipeline that **passes** the transitive endpoint check can still have a dangerous
   intermediate hop — `transitive_safety_misses_intermediate` proves this with a concrete
   witness.
- A pipeline that **passes** every individual hop check can still have insecure endpoints
   — `hopwise_safe_not_implies_transitive_safe` proves this in the other direction.

The `--medical-demo` path in the PoC exercises exactly the first case: `isTransitivelySafe`
returns `true` (the endpoints look fine), but `isHopwiseSafe` returns `false` (the
`High → Medium → Low` intermediate hop violates the lattice). This is the distinction
between a policy audit that only checks source and destination versus one that inspects
every data-sharing hop independently.

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

### The Free Monad Model

`Prog` is a **free monad** over `AgentEffect` — the standard way to represent effectful
programs as pure data structures in functional programming and type theory. A `Prog`
value is either a pure return value or an effect constructor (`WebSearch`, `CodeExec`,
`ReadDB`, `SendEmail`, `ExfilData`) paired with a continuation. This representation
allows us to reason about what a program *does* (its effects) without ever running it.

`SafeProg` is an inductive safety predicate over the `Prog` tree. It is defined by
recursion on the structure of the program: a `pure` computation is always safe, and
an `effect f k` computation is safe if the effect's capability is in `contract.base ∖
contract.forbidden` and every continuation `k a` is also safe. The result is a
**compositional**, program-level safety certificate.

### Bridge to Layer 1

| Theorem | Plain English |
|---|---|
| `safeProg_caps_in_base` | Every effect in a SafeProg-safe program uses only caps in `contract.base` |
| `safeProg_base_forbidden_disjoint` | Every used cap is in `base \ forbidden` |
| `safeProg_implies_capSafe_empty_edges` | **Adequacy:** SafeProg-safe + disjoint contract → `isCapSafe [] = true` |
| `safeProg_does_not_imply_capSafe` | **Independence:** SafeProg is a program-level check; `isCapSafe` is a contract-level check — both are needed and neither implies the other in general |

`safeProg_does_not_imply_capSafe` is a *separation of concerns* theorem. It says that
even a provably-safe program (per `SafeProg`) can be deployed in a context where the
hyperedge environment causes capability emergence — the program itself is fine, but
the *composition* of the environment with the program's contract is not. Layer 3 is
therefore not a replacement for Layer 1; it is a complementary check at a different
level of abstraction.

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

`validPipeline_iff` is the only biconditional theorem in the project. Every other layer
proves one direction (safety implies some property, or some property implies unsafety).
Layer 4 closes the loop: `ValidPipeline P ↔ capSafe ∧ ifcSafe` means the certificate
is **both sound** (no false approvals) **and complete** (no false rejections for pipelines
that genuinely satisfy both conditions). This is the mathematical content of "compile-time
guarantee": if your pipeline builds with a `ValidPipeline` certificate, it is provably
safe; if it does not build, it is provably not certifiable under the current spec.

`trustedPipeline_valid` is the existence proof — it shows that safe pipelines are not an
empty class. A concrete pipeline that satisfies both conditions is constructed and its
certificate is machine-checked, confirming the system is neither vacuously sound (no
pipeline ever passes) nor vacuously complete (every pipeline passes).

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

## Layer 5 — Cedar Concrete Counterexample (`CedarBridge.lean`)

**The idea:** Cedar is Amazon's production authorization language — formally verified,
used in AWS, and the current state of the art in deployed AI access control. `CedarBridge`
defines a minimal but faithful embedding of Cedar's evaluation model — `CedarPolicy`,
`CedarRequest`, `CedarDecision`, `cedarEval` — and then constructs **concrete Cedar
policies** for the demo agents. It proves that Cedar is *sound*: the policies it writes
correctly deny what they are supposed to deny. Then it proves the critical gap: Cedar's
correct denial for each individual agent is *not sufficient* to detect that the composed
team can exfiltrate data.

| Theorem | Plain English |
|---|---|
| `cedar_nonCompositionality_gap` | Cedar denies exfilData for every individual principal ∧ FlowGuard proves the composed team has exfilData in its closure |
| `cedar_ifc_gap` | Cedar approves every hop in the medical pipeline ∧ FlowGuard proves the transitive flow is insecure |
| `cedar_is_incomplete` | **Master result:** Cedar is sound but incomplete — both gaps checked simultaneously |
| `cedarAware_strictly_weaker` | Cedar approves the pipeline; FlowGuard rejects it — FlowGuard is strictly stronger |

`cedar_is_incomplete` is a **conjunction**: it proves both the capability-emergence gap
and the IFC gap in a single theorem. This is the "master" Cedar result — the one that
would appear in a paper abstract.

---

## Layer 6 — Cedar Structural Impossibility (`CedarIncompleteness.lean`)

**The idea:** `CedarBridge` showed Cedar *fails* on the concrete examples. `CedarIncompleteness`
proves *why Cedar must fail* — not because of any specific policy choice, but because of
a fundamental mismatch between Cedar's input model and the information required for pipeline
safety analysis.

The argument has three steps, each formalised as a theorem:

1. **Cedar is request-local** — `cedar_is_request_local` and `cedar_request_determines_decision`
    establish that Cedar's decision depends only on `(principal, action, resource)`. No Cedar
    policy can inspect a `Finset Cap` or a `List HyperEdge`. This is enforced at the **type
    level**: `CedarPolicy := CedarRequest → CedarDecision`.

2. **Capability closure is not request-local** — `emergence_requires_joint_inspection` and
    `joint_closure_strictly_larger` prove that whether `exfilData` emerges requires inspecting
    the *joint* base capability set of both agents together. This information is not encoded in
    any individual `CedarRequest`.

3. **Therefore Cedar cannot be complete** — `cedar_incomplete_universally` and
    `cedar_capability_separation` prove that for *any* Cedar policy, there exists an unsafe
    composition it cannot detect.

| Theorem | Plain English |
|---|---|
| `cedar_is_request_local` | Cedar's decision is a pure function of the request — type-enforced |
| `cedar_request_determines_decision` | Same (principal, action, resource) → same decision, always |
| `cedar_blind_to_capsets` | Two agents sharing a principal name are Cedar-indistinguishable on any request — the blindness is not a policy gap, it is enforced by the type of `CedarPolicy` |
| `cedar_capability_separation` | FlowGuard gives different verdicts for webAgent alone vs webAgent+execAgent; Cedar gives identical decisions — this is the separation theorem |
| `joint_closure_strictly_larger` | `exfilData ∉ closure(webAgent)` ∧ `exfilData ∉ closure(execAgent)` ∧ `exfilData ∈ closure(webAgent ∪ execAgent)` — the information gap in one theorem |
| `emergence_requires_joint_inspection` | You cannot detect capability emergence by inspecting agents one at a time |
| `closure_union_ge_union_closures` | `closure(A) ∪ closure(B) ⊆ closure(A ∪ B)` — monotonicity of composition |
| `cedar_incomplete_universally` | For any agents where composition is unsafe, no Cedar policy can detect it |

The comment in the source is worth quoting directly: *"This is not a criticism of Cedar.
Cedar is designed for per-request authorization. It is a theorem about the fundamental
mismatch between Cedar's input model and the information required for pipeline safety."*

---

## The PoC Pipeline — How It Works

The Python PoC is not a reimplementation of the Lean proofs in Python. It is a
**dynamic front-end** that: (a) reads real agent source files and infers their capability
specifications, (b) runs the same logical checks as the Lean formalisation using a Python
implementation of the same algorithms, and (c) queries the compiled Lean files at runtime
to cite the exact theorem — with its verbatim statement text — that covers each finding.

### Capability Extraction (`extractor.py`)

The extractor infers an `AgentSpec` from a Python source file. It operates in three modes:

- **`ast` mode** — walks the Python AST, matches function calls and attribute access
   patterns (e.g., `requests.get(...)` → `webSearch`, `subprocess.run(...)` → `codeExec`,
   `smtplib.SMTP(...)` → `sendEmail`), and applies filename heuristics as a secondary
   signal. Fully offline; no credentials required.
- **`llm` mode** — sends the source file to Gemini 2.0 Flash with a structured prompt
   requesting a JSON `AgentSpec`. Produces richer semantic inference (catches higher-level
   patterns that AST walks miss), but requires a `GEMINI_API_KEY` in `.env`.
- **`both` mode** — runs AST extraction first, passes the result as a structured prior
   into the LLM prompt, and merges the outputs. This is the most accurate mode because the
   LLM receives concrete AST evidence to confirm or expand.

The extractor also infers `pipeline_channels` for the IFC layer: a list of
`(src_label, dst_label)` tuples representing data-sharing steps in the agent file.

### Verification Engine (`verifier.py` + `hyperedges.py`)

`hyperedges.py` implements the core algorithms as a direct mirror of the Lean formalisation:

| Python function | Lean theorem it mirrors |
|---|---|
| `cap_closure(edges, base)` | `capClosure` fixed-point iteration (CapHypergraph) |
| `is_cap_safe(edges, agent)` | `isCapSafe` (CapHypergraph) |
| `compose_list(agents)` | `compose` + `coalition_nonCompositionality_universal` (CapHypergraph) |
| `get_fired_edges(edges, agent)` | hyperedge premise check (CapHypergraph) |
| `is_transitively_safe(channels)` | `isTransitivelySafe` (InfoFlow) |
| `is_hopwise_safe(channels)` | `isHopwiseSafe` (InfoFlow) |
| `cedar_team_eval(cap, policies)` | `cedarEval` (CedarBridge) |

`verifier.py` orchestrates the three-phase check: individual safety per agent, composition
with hyperedge closure, and Cedar comparison. It produces a structured result dict that is
consumed by both the terminal reporter (`analyze.py`) and the HTML dashboard.

The hyperedge library (`HYPEREDGE_LIBRARY` in `hyperedges.py`) is **not hardcoded to the
demo agents**. It is a general-purpose library of capability interaction rules. Running the
PoC on any Python agent file will apply the same closure rules to whatever capabilities the
extractor infers — the demo is just a concrete entry point into a general system.

### Live Lean Bridge (`lean_bridge.py`)

This is what makes the PoC dynamic rather than a static display:

- **`extract_theorems(lean_file)`** — reads a compiled `.lean` file with a regex over
   theorem/lemma declarations, extracting name, statement text (up to 400 characters), and
   the preceding docstring. This runs against the actual source files in the repo, not a
   cached snapshot.
- **`get_all_theorems()`** — indexes all 6 `.lean` files at startup, building a dict
   `{filename: [theorem_dicts]}`.
- **`verify_demo_in_lean()`** — writes a temporary `.lean` file containing `#eval` and
   `#check` calls, invokes `lake env lean` as a subprocess, and matches the Lean kernel's
   output against expected values. This is a live round-trip: the kernel re-evaluates
   `isCapSafe demoEdges webAgent`, `isCapSafe demoEdges (compose webAgent execAgent)`,
   and `cedarEval teamPolicy {...}` from scratch on every run.

When the terminal output says `↑ text read directly from CapHypergraph.lean`, it means
exactly that: the theorem statement was parsed from the file on disk in that run, not
retrieved from any database or hardcoded string in the Python source.

### Running on Your Own Agents

The `--demo` flag is a shorthand for two specific files in `poc/sample_agents/`. The PoC
accepts any Python files directly:
### Extending the PoC

The current PoC is a solid foundation for more complex versions. Natural next steps include:

- **New hyperedge rules** — adding entries to `HYPEREDGE_LIBRARY` in `hyperedges.py`
   immediately extends the capability interaction model without any change to the verifier
   or bridge. New rules should ideally be mirrored by a corresponding theorem in `CapHypergraph.lean`.
- **New agent types** — adding a new Python file to `poc/sample_agents/` and running it
   through the extractor. The system handles coalitions of arbitrary size via `compose_list`.
- **Richer IFC labelling** — the current IFC layer uses a three-level lattice
   (`low < medium < high`). Extending `InfoFlow.lean` to a four-level or lattice-ordered
   poset would require updating `is_transitively_safe` and `is_hopwise_safe` in `hyperedges.py`
   to match.
- **LLM-based hyperedge inference** — rather than a fixed library, a future version could
   prompt an LLM to propose candidate hyperedges from the agent descriptions, then verify
   the proposed edges against the Lean closure theorems.
- **Automated Lean proof generation** — `lean_bridge.py` already writes and evaluates
   temporary `.lean` files. A natural extension would generate a fresh `#eval` check for
   each new composition at runtime, making the Lean verification truly dynamic rather than
   limited to the five pre-defined `DEMO_CHECKS`.
- **Integration with real orchestration frameworks** — `extractor.py` currently reads
   standalone Python files. Adding parsers for LangChain agent definitions, AutoGen
   `ConversableAgent` configs, or CrewAI task YAML files would make FlowGuard applicable
   to production multi-agent deployments without any change to the core verification logic.

---

## Why This Matters

Current AI safety tools — guardrails, red-teaming, constitutional AI — almost universally
evaluate agents **in isolation**. FlowGuard demonstrates, with machine-checked mathematical
proof, that this is insufficient.

- **AI governance frameworks** that certify individual models are incomplete without compositional guarantees.
- **Multi-agent orchestration platforms** (LangChain, AutoGen, CrewAI) need pipeline-level safety analysis, not just per-agent evaluation.
- **Production authorization languages** (Cedar, OPA, RBAC) have structural blind spots for emergent capabilities — FlowGuard proves this, not merely argues it.
- **Formal verification** of AI systems is tractable today — the proofs in this repository compile, are machine-checked, and can be extended.
- **The PoC demonstrates production tractability** — FlowGuard's verification pipeline
   runs on real Python agent source files today, infers capability specifications without
   manual annotation, and cites machine-checked theorems against its findings. This is not
   a research prototype requiring a PhD to operate.
- **Dynamic theorem citation bridges formal and operational** — the PoC reads theorem
   statement text live from the compiled `.lean` files on each run. Every verdict is
   traceable to a specific line of machine-checked mathematics, not to a hardcoded string
   in the analysis tool.

## Theorem Index

| Theorem | File | What it proves |
|---|---|---|
| `capClosure_mono` | CapHypergraph | S ⊆ T → capClosure(S) ⊆ capClosure(T) |
| `capClosure_extensive` | CapHypergraph | S ⊆ capClosure(S) — base caps always survive |
| `capClosure_is_fixpoint` | CapHypergraph | step(capClosure(S)) = capClosure(S) — convergence |
| `capClosure_is_least_fixpoint` | CapHypergraph | capClosure is the **smallest** closed superset |
| `webAgent_is_safe` | CapHypergraph | Web-search agent alone cannot exfiltrate |
| `execAgent_is_safe` | CapHypergraph | Code-execution agent alone cannot exfiltrate |
| `composedTeam_is_unsafe` | CapHypergraph | Composed team: `exfilData` enters closure |
| `nonCompositionalityCounterexample` | CapHypergraph | Both safe individually ∧ unsafe together (concrete) |
| `nonCompositionality_exists` | CapHypergraph | ∃-form: there exist edges and agents where safety fails to compose |
| `nonCompositionality_universal` | CapHypergraph | ∀-form: for any edges and agents fitting structural premises, composition is unsafe |
| `coalition_nonCompositionality_universal` | CapHypergraph | ∀ agent lists: any dangerous pair poisons the whole coalition |
| `safeRegion_downward_closed` | CapHypergraph | Smaller base set → at least as safe |
| `safeRegion_closed_under_intersection` | CapHypergraph | Intersection of two safe base sets is safe (Moore family) |
| `compose_forbidden_union_justified` | CapHypergraph | Union of forbidden sets is correct composition semantics |
| `nonInterference_nonCompositional` | InfoFlow | All local hops approved ∧ transitive flow globally unsafe |
| `localApproval_not_transitive` | InfoFlow | ∃-form: local approval fails to compose |
| `secureFlow_transitive` | InfoFlow | The global security lattice IS transitive — the flaw is in local policy |
| `insecure_flows_characterised` | InfoFlow | Complete characterisation: exactly 3 downward flows are insecure |
| `cascaded_declassification_parametric` | InfoFlow | ∀ policies approving a downward two-hop chain → compositionally dangerous |
| `medical_hops_dangerous_for_any_policy` | InfoFlow | Even a maximally restrictive two-hop policy is provably dangerous |
| `transitive_safety_misses_intermediate` | InfoFlow | ∃ pipeline: `isTransitivelySafe = true` yet `isHopwiseSafe = false` |
| `hopwise_safe_not_implies_transitive_safe` | InfoFlow | ∃ pipeline: `isHopwiseSafe = true` yet `isTransitivelySafe = false` |
| `isTransitivelySafe_only_checks_endpoints` | InfoFlow | ∀ good-endpoint pipelines pass transitive check regardless of middle |
| `hopwise_is_necessary_for_intermediate_safety` | InfoFlow | Only `isHopwiseSafe` catches interior violations |
| `bindSafe` | AgentProgram | SafeProg is closed under monadic bind |
| `safeProg_implies_capSafe_empty_edges` | AgentProgram | SafeProg-safe + disjoint contract → `isCapSafe [] = true` |
| `safeProg_does_not_imply_capSafe` | AgentProgram | SafeProg and isCapSafe are independent checks (separation of concerns) |
| `validPipeline_iff` | FlowCheck | `ValidPipeline P ↔ capSafe ∧ ifcSafe` — biconditional certificate |
| `flowguard_sound` | FlowCheck | `ValidPipeline P` → both guarantees hold |
| `flowguard_complete` | FlowCheck | Both guarantees hold → construct a `ValidPipeline` certificate |
| `trustedPipeline_valid` | FlowCheck | A concrete pipeline **does** receive a full certificate |
| `hopwiseValidPipeline_full_certificate` | FlowCheck | Three-way certificate: cap + hopwise IFC + transitive IFC |
| `validPipeline_hierarchy` | FlowCheck | `HopwiseValidPipeline → ValidPipeline`, not vice versa |
| `cedar_is_request_local` | CedarIncompleteness | Cedar's decision is a pure function of the request — type-enforced |
| `cedar_blind_to_capsets` | CedarIncompleteness | Same-name agents are Cedar-indistinguishable on any request |
| `cedar_capability_separation` | CedarIncompleteness | FlowGuard gives different verdicts for webAgent vs composed team; Cedar gives identical decisions |
| `joint_closure_strictly_larger` | CedarIncompleteness | `exfilData` absent from individual closures but present in joint closure |
| `emergence_requires_joint_inspection` | CedarIncompleteness | Cannot detect capability emergence by inspecting agents one at a time |
| `closure_union_ge_union_closures` | CedarIncompleteness | `closure(A) ∪ closure(B) ⊆ closure(A ∪ B)` — monotonicity |
| `cedar_incomplete_universally` | CedarIncompleteness | ∀ agents where composition is unsafe, no Cedar policy can detect it |
| `cedar_nonCompositionality_gap` | CedarBridge | Cedar denies ∧ FlowGuard detects emergence — concrete gap |
| `cedar_ifc_gap` | CedarBridge | Cedar approves every medical hop ∧ FlowGuard proves transitive flow insecure |
| `cedar_is_incomplete` | CedarBridge | Cedar is sound but incomplete — both gaps machine-checked simultaneously |
| `cedarAware_strictly_weaker` | CedarBridge | Cedar approves pipeline; FlowGuard rejects it — FlowGuard strictly stronger |

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