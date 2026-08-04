/-
# Step 2b: Expected return over an unbounded future

What the agent expects when the interaction never ends.

## The idea

Take the bounded-horizon returns from the previous file and let the horizon grow
without limit. If those numbers settle down to something, that limit is the
infinite-horizon return.

They do settle down, and the reason is a standard fact about real numbers: a
sequence that is **increasing** and **bounded above** always converges. We
establish both halves here:

* increasing -- `expectedReturn_mono_horizon_of_stationary` from the previous
  file;
* bounded above -- `expectedReturn_le_maxPossible` below, which upgrades the
  horizon-dependent geometric bound to one that does not depend on the horizon
  at all.

## Why only stationary policies

This is forced by the countdown convention, not chosen for convenience.

`Policy` takes the number of cycles *remaining*. So extending the horizon
changes what a non-stationary policy does at **every** step: the sequence
`n ↦ expectedReturn ν γ π n h` compares genuinely different behaviours rather
than successively longer runs of one behaviour. There is nothing for it to
converge to.

For `Policy.ofStationary f` the horizon argument is ignored, extending the
horizon really does just append more future, and everything works.

This restriction looks like a limitation. It is not: the infinite-horizon
*optimal* policy turns out to be stationary (see `Agent/InfiniteHorizon.lean`),
so these results apply to exactly the agent we care about.

## Why `γ < 1` appears here and not before

Bounded horizons are bounded by `1 + γ + ... + γⁿ⁻¹` for any `γ ≥ 0`; that sum
is finite because it has finitely many terms. An unbounded horizon needs the
*infinite* series to converge, which is exactly the condition `γ < 1`.

## Supremum as the definition, convergence as a theorem

`expectedReturnForever` is defined as a supremum (`⨆`), not a limit. A supremum
is well-defined from boundedness alone, whereas a limit requires convergence to
be proved first. The two coincide -- `tendsto_expectedReturnForever` proves it --
but defining by supremum means later results never carry a convergence
hypothesis they do not need.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import UAI.Returns.FiniteHorizon

namespace UAI

open scoped BigOperators
open Filter Topology

variable {A E : Type*} [Fintype E] [HasReward E]

/-- The largest return that is possible at all, for a given discount factor.

Equal to `1 / (1 - γ)`. This is what you would get from a perfect reward of 1 at
every step, forever, discounted geometrically. Named so that bounds elsewhere
read as statements about a meaningful quantity rather than an opaque
expression. -/
noncomputable def maxPossibleReturn (γ : ℝ) : ℝ := (1 - γ)⁻¹

section Bounds

variable {ν : Environment A E} {γ : ℝ} {π : Policy A E}

/-- **Expected return is bounded by `maxPossibleReturn`, uniformly in the
horizon.**

The previous file's bound grows with the horizon; this one does not. That is
exactly what is needed for the supremum over *all* horizons to be finite, which
is what makes the next section possible.

Proof idea: the finite geometric sum is a partial sum of the infinite geometric
series, which converges to `1 / (1 - γ)` when `γ < 1`. -/
theorem expectedReturn_le_maxPossible (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (n : ℕ) (h : History A E) :
    expectedReturn ν γ π n h ≤ maxPossibleReturn γ := by
  have hsummable : Summable fun i : ℕ => γ ^ i :=
    summable_geometric_of_lt_one hγ hγ1
  have hpartial : ∑ i ∈ Finset.range n, γ ^ i ≤ ∑' i : ℕ, γ ^ i :=
    hsummable.sum_le_tsum _ (fun i _ => pow_nonneg hγ i)
  calc expectedReturn ν γ π n h ≤ ∑ i ∈ Finset.range n, γ ^ i :=
        expectedReturn_le_geometricSum hb hγ n h
    _ ≤ ∑' i : ℕ, γ ^ i := hpartial
    _ = maxPossibleReturn γ := tsum_geometric_of_lt_one hγ hγ1

end Bounds

section Stationary

variable {ν : Environment A E} {γ : ℝ}

/-- The bounded-horizon returns of a stationary policy, viewed as a sequence
indexed by the horizon.

Introduced as a named object so that the two hypotheses of the convergence
theorem -- monotone, bounded above -- can be stated about it directly. -/
noncomputable def expectedReturnSeq (ν : Environment A E) (γ : ℝ)
    (f : History A E → A) (h : History A E) : ℕ → ℝ :=
  fun n => expectedReturn ν γ (Policy.ofStationary f) n h

/-- First half of convergence: the sequence is increasing. -/
theorem expectedReturnSeq_monotone (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (f : History A E → A) (h : History A E) :
    Monotone (expectedReturnSeq ν γ f h) :=
  monotone_nat_of_le_succ fun n =>
    expectedReturn_mono_horizon_of_stationary hb hγ f n h

/-- Second half of convergence: the sequence is bounded above.

The bound is `maxPossibleReturn γ`, and crucially it does not depend on `n`. -/
theorem expectedReturnSeq_bddAbove (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (hγ1 : γ < 1) (f : History A E → A) (h : History A E) :
    BddAbove (Set.range (expectedReturnSeq ν γ f h)) := by
  refine ⟨maxPossibleReturn γ, ?_⟩
  rintro x ⟨n, rfl⟩
  exact expectedReturn_le_maxPossible hb hγ hγ1 n h

/-- **Expected return over an unbounded future**, for a stationary policy. -/
noncomputable def expectedReturnForever (ν : Environment A E) (γ : ℝ)
    (f : History A E → A) (h : History A E) : ℝ :=
  ⨆ n : ℕ, expectedReturnSeq ν γ f h n

/-- Every bounded horizon underestimates the unbounded one. -/
theorem expectedReturn_le_forever (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (hγ1 : γ < 1) (f : History A E → A) (n : ℕ) (h : History A E) :
    expectedReturn ν γ (Policy.ofStationary f) n h
      ≤ expectedReturnForever ν γ f h :=
  le_ciSup (expectedReturnSeq_bddAbove hb hγ hγ1 f h) n

/-- The unbounded-horizon return obeys the same ceiling. -/
theorem expectedReturnForever_le_maxPossible (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (f : History A E → A) (h : History A E) :
    expectedReturnForever ν γ f h ≤ maxPossibleReturn γ :=
  ciSup_le fun n => expectedReturn_le_maxPossible hb hγ hγ1 n h

/-- The unbounded-horizon return is never negative. -/
theorem expectedReturnForever_nonneg (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (f : History A E → A) (h : History A E) :
    0 ≤ expectedReturnForever ν γ f h := by
  refine le_trans ?_ (expectedReturn_le_forever hb hγ hγ1 f 0 h)
  simp

/-- **The bounded-horizon returns genuinely converge to the unbounded one.**

This is what justifies calling `expectedReturnForever` a *return* rather than
merely an upper bound: the sequence is increasing and bounded, so its supremum
is also its limit. Without this theorem the definition would be suggestive
naming and nothing more. -/
theorem tendsto_expectedReturnForever (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (f : History A E → A) (h : History A E) :
    Tendsto (expectedReturnSeq ν γ f h) atTop
      (𝓝 (expectedReturnForever ν γ f h)) :=
  tendsto_atTop_ciSup (expectedReturnSeq_monotone hb hγ f h)
    (expectedReturnSeq_bddAbove hb hγ hγ1 f h)

end Stationary

end UAI
