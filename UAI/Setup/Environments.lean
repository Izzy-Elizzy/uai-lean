/-
# Step 1d: Environments

What the *world* is, mechanically.

## The definition

An environment says: given everything that has happened, and given the action
the agent just took, how likely is each possible next percept?

    probability : History A E → A → E → ℝ≥0∞

That is the whole object. No state, no transition matrix, no dynamics model --
just a conditional distribution over next percepts given the entire past.

## Why "semimeasure" and not "measure": the halting problem

A probability *measure* would require the probabilities to sum to exactly one:
something always happens. We require only

    ∑ over percepts e of probability h a e  ≤  1

so probability is allowed to go *missing*. That looks like a strange thing to
permit. It is forced.

Environments in this theory are ultimately **programs**. To ask what an
environment predicts, you run a Turing machine. But a Turing machine might not
halt. If the program computing the next percept runs forever, no percept is
produced, and that probability mass simply vanishes. The missing mass is exactly
the probability of non-halting.

Why not just exclude the non-halting programs and keep proper measures? Because
halting is **undecidable**. You cannot enumerate the computable measures --
deciding which programs qualify would solve the halting problem. But you *can*
enumerate the lower-semicomputable semimeasures, precisely because the
badly-behaved ones are allowed to leak mass instead of having to be excluded.

That enumerability is the whole ballgame: it is what makes the universal mixture
in `UniversalPrior/` possible. So the deficiency is not a technical convenience.
It is the price the halting problem charges for having a universal prior at all.

## Chronology is enforced by the type, not by a side condition

An environment must not react to actions that have not happened yet. Textbooks
state this as a side condition and then carry it around. Here it is structural:
the function is only ever *given* the past history and the current action, so it
has no argument through which a future action could be mentioned. The condition
is impossible to violate and therefore never needs stating.

## Why `ℝ≥0∞` for probabilities

Three reasons. It makes `≤ 1` natural with no coercion friction; it makes
infinite sums unconditionally well-defined (needed in `UniversalPrior/`); and it
matches the algorithmic-information library this development builds on, so the
two meet without translation.

Rewards and returns, by contrast, are plain reals -- see
`Returns/FiniteHorizon.lean` for why that split is deliberate.
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import UAI.Setup.Histories

namespace UAI

open scoped ENNReal BigOperators

/-- An environment: given the history so far and the action just taken, a
sub-probability distribution over the next percept. -/
structure Environment (A E : Type*) [Fintype E] where
  /-- The probability of percept `e` after history `h` and action `a`. -/
  probability : History A E → A → E → ℝ≥0∞
  /-- Total probability over all percepts is at most one.

  Not *equal* to one: mass may be lost to non-halting programs. See the file
  header for why this weakening is forced rather than chosen. -/
  totalProbabilityAtMostOne :
    ∀ (h : History A E) (a : A), ∑ e : E, probability h a e ≤ 1

namespace Environment

variable {A E : Type*} [Fintype E]

/-- Any single probability is at most one.

Proof idea: one percept's probability, plus the probabilities of all the others,
equals the total; probabilities are never negative; the total is at most one. -/
theorem probability_le_one (ν : Environment A E) (h : History A E) (a : A)
    (e : E) :
    ν.probability h a e ≤ 1 := by
  classical
  have hsplit :
      ν.probability h a e + ∑ e' ∈ Finset.univ.erase e, ν.probability h a e'
        = ∑ e' : E, ν.probability h a e' :=
    Finset.add_sum_erase Finset.univ (fun e' => ν.probability h a e')
      (Finset.mem_univ e)
  calc ν.probability h a e
      ≤ ν.probability h a e + ∑ e' ∈ Finset.univ.erase e, ν.probability h a e' :=
        self_le_add_right _ _
    _ = ∑ e' : E, ν.probability h a e' := hsplit
    _ ≤ 1 := ν.totalProbabilityAtMostOne h a

/-- Probabilities are never infinite.

`ℝ≥0∞` contains a genuine `⊤` (infinity), and arithmetic with `⊤` misbehaves
(infinity times zero, infinity minus infinity). This lemma rules that corner out
once, so later proofs never have to handle it. It is what justifies converting
probabilities to ordinary reals in `Returns/FiniteHorizon.lean`. -/
theorem probability_ne_top (ν : Environment A E) (h : History A E) (a : A)
    (e : E) :
    ν.probability h a e ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (ν.probability_le_one h a e)

/-- How much probability mass an environment loses at a given history and
action. Zero exactly when the environment is a genuine probability measure
there.

Not used in any proof. It exists so that the semimeasure/measure gap is a
first-class object a reader can point at, rather than an implicit fact buried in
an inequality. -/
noncomputable def deficiency (ν : Environment A E) (h : History A E) (a : A) :
    ℝ≥0∞ :=
  1 - ∑ e : E, ν.probability h a e

/-- A deterministic environment: it replies to each history-action pair with one
fixed percept, with certainty.

This is a **sanity check**, not a mathematically interesting object. Its purpose
is to prove that `Environment` is inhabited -- that the conditions in the
structure are simultaneously satisfiable and we have not accidentally defined an
empty type. -/
def deterministic [DecidableEq E] (f : History A E → A → E) :
    Environment A E where
  probability h a e := if e = f h a then 1 else 0
  totalProbabilityAtMostOne := by
    intro h a
    have heq : (∑ e : E, if e = f h a then (1 : ℝ≥0∞) else 0) = 1 := by
      have := Finset.sum_eq_single_of_mem
        (f := fun e => if e = f h a then (1 : ℝ≥0∞) else 0)
        (f h a) (Finset.mem_univ _) (fun b _ hb => if_neg hb)
      simpa using this
    simp [heq]

/-- The environment that loses *all* its probability mass: it never replies at
all.

A second sanity check, in the opposite direction. `deterministic` witnesses that
proper measures are expressible; this one witnesses that the `≤ 1` requirement
is genuinely weaker than `= 1`, since this object satisfies the former and
badly fails the latter. -/
def bottom : Environment A E where
  probability _ _ _ := 0
  totalProbabilityAtMostOne := by
    intro h a
    simp only [Finset.sum_const_zero]
    exact zero_le_one

end Environment

end UAI
