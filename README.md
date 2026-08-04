# Universal Artificial Intelligence in Lean 4

A machine-checked formalisation of AIXI - Hutter's theoretical model of a
maximally intelligent agent - built from first principles.

**Status: work in progress, first release.** Every theorem currently in the
repo is verified by the Lean kernel -- no `sorry`, no axioms, no `admit`, no
`native_decide` -- but "verified" only means the proofs are correct given the
definitions. It does not mean the definitions are the right ones, that nothing
is missing, or that the overall approach is the best one. This is a first pass,
not a finished artifact, and it should be read and used that way.

Author: Iizalaarab Elhaimeur, Department of Computer Science, Old Dominion
University.

Developed with substantial assistance from Claude (Anthropic) for Lean 4
implementation.

---

## What this is

A construction of AIXI in five steps, each building on the last:

| Step | Folder | Question answered |
|---|---|---|
| 1 | `Setup/` | What are agents, worlds, and the messages between them? |
| 2 | `Returns/` | Given a policy, how much reward should we expect? |
| 3 | `Optimality/` | How well is it *possible* to do, and how? |
| 4 | `UniversalPrior/` | How do you act without knowing which world you are in? |
| 5 | `Agent/` | AIXI = Step 3's answer applied to Step 4's environment |

## Main results

- **Bellman optimality (bounded horizon)** - `Optimality/FiniteHorizon.lean`.
  The greedy policy attains the best achievable return, and no policy exceeds
  it.
- **The Bellman fixed-point equation (unbounded horizon)** -
  `Optimality/InfiniteHorizon.lean`. This is the central theorem: it is what
  makes an infinite-horizon optimal policy definable at all.
- **A weighted blend of environments is an environment** -
  `UniversalPrior/Mixtures.lean`, with a domination bound.
- **The complexity-weighted universal environment** -
  `UniversalPrior/ComplexityWeights.lean`, built on genuine prefix Kolmogorov
  complexity via the Kraft inequality.
- **AIXI, and that it is stationary** - `Agent/InfiniteHorizon.lean`.

## Two things worth knowing

**Infinite horizon without Banach.** The textbook route to a fixed-point value
function needs a complete metric space and a contraction argument. We avoid it
entirely: the *best* return is monotone in the horizon (unlike a fixed policy's
return, which is not), so monotone-plus-bounded gives convergence directly. The
fixed point then follows from a limit interchange rather than a contraction.

**Minimal hypotheses, found by the linter.** The attainment half of Bellman
optimality needs *no* assumptions about rewards or the discount, and soundness
needs only `0 ≤ γ`. We discovered this because Lean's unused-variable linter
flagged hypotheses we had assumed were necessary.

---

## What this does NOT claim

This section matters more than the results list. Please read it before citing
this work.

**1. The environment family is an input, not a construction.**
`universalEnvironment` takes a family of candidate environments as a parameter.
Constructing an actual enumeration of the lower-semicomputable chronological
semimeasures is genuine computability theory and is not attempted here. So the
honest claim is "universal *for the family it is given*", not "universal for all
computable environments".

**2. Optimality here is with respect to the universal environment.** Since that
environment is what defines the agent, these results are close to true by
construction. They do **not** establish that AIXI performs well against the true
environment.

**3. That stronger claim is known to fail.** Leike & Hutter, *Bad Universal
Priors and Notions of Optimality* (COLT 2015), show adversarial choices of
reference machine make AIXI misbehave drastically, and that no invariance
theorem is known for AIXI - unlike Kolmogorov complexity, which has one. In the
finite-lifetime case, for any policy there is a prior making it uniquely
optimal, which renders such guarantees vacuous.

**4. Nothing here is computable.** Everything is `noncomputable`, as expected
for AIXI-adjacent objects. This formalisation does not and cannot make AIXI
runnable.

**The honest summary:** this is *verified infrastructure*. Its value is less in
the theorems proved - several are near-definitional - than in what becomes
statable on top of it.

---

## Design decisions, and why

Each is documented at length in the file that realises it.

| Decision | Where | Why |
|---|---|---|
| Environments are **semimeasures**, not measures | `Setup/Environments.lean` | Programs may not halt, and halting is undecidable, so the computable *measures* are not enumerable while the semimeasures are |
| Chronology enforced **structurally** | `Setup/Environments.lean` | The type never supplies future actions, so the side condition cannot be violated |
| Policies are **non-stationary** | `Setup/Policies.lean` | Optimal finite-horizon policies genuinely depend on time remaining |
| Rewards **detachable** from percepts | `Setup/Rewards.lean` | Lets future work generalise to history-level objectives without a rewrite |
| Bounded rewards as a **hypothesis**, not a type | `Setup/Rewards.lean` | Keeps theorems that do not need it general - and lets the linter reveal which those are |
| Probabilities `ℝ≥0∞`, returns `ℝ` | `Returns/FiniteHorizon.lean` | `ℝ≥0∞` subtraction is truncated and would corrupt return comparisons; `ℝ` infinite sums need convergence conditions everywhere |
| Mixture weights **abstract** | `UniversalPrior/Mixtures.lean` | Decouples the blend theorem from any complexity API; swapping weights touches one thin file |

## Dependencies

- Lean 4 with Mathlib
- `KolmogorovMathlib` (Alexey Milovanov's algorithmic information theory
  library), used for the dyadic weight sequence and the Kraft inequality for
  prefix complexity

## Getting started

Read in the order given by the table above; each file's header explains what it
does and why before any Lean appears. Start with `Setup/Rewards.lean`.

## Contributing

Issues and pull requests welcome, especially issues. If you spot an error, a
bad definition, a gap in the reasoning, or anywhere this README overstates what
is actually proved, please say so. I would much rather be corrected than have
something wrong sit here looking polished.

If any part of this project overlaps with work you or someone else in the
community is already doing, please reach out. I want this to add to the
community's work, not step on it.
