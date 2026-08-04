/-
# Step 4a: Blending many environments into one

## The problem this solves

An agent does not know which environment it is in. The AIXI answer: do not pick
one -- consider all of them at once, weighted by how plausible they are, and act
against the blend.

This file proves the one structural fact that makes that legitimate:

> A weighted blend of environments is itself an environment.

## Why the weights are abstract here

The famous choice of weights is `2^(-K(ν))`, where `K` is Kolmogorov complexity:
simpler environments get more weight. That is Occam's razor, made mathematical.

But notice: **nothing about proving the blend is a valid environment depends on
the weights being complexity-derived.** All that is needed is that the weights
are non-negative and sum to at most one. So this file proves the theorem for
*arbitrary* weights, and the specific choices live in the two files beside it.

That separation is deliberate and it paid off. It means the mathematical content
here has no dependency on any algorithmic-information library, and swapping one
weighting scheme for another touches only a thin instantiation file, never this
one.

## Why weights sum to *at most* one, not exactly one

The Kraft inequality -- the theorem that guarantees complexity weights are
summable at all -- gives `∑ 2^(-K(ν)) ≤ 1`, not equality. Requiring equality
here would rule out the intended instantiation.

## Why `ℝ≥0∞` makes this easy

Over the extended non-negative reals, *every* family is summable and infinite
sums need no convergence side conditions. That is why the blend can be taken
over an arbitrary index type with no summability hypothesis anywhere.

## The other theorem here: domination

`weight_mul_le_combine` says the blend assigns each ingredient environment at
least `(its weight) × (what that environment assigns)`. This is what makes
blends *useful* rather than merely well-defined: it bounds how badly an agent
using the blend can be misled relative to using the truth.
-/

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import UAI.Setup.Environments

namespace UAI

open scoped ENNReal BigOperators

variable {A E : Type*} [Fintype E]

/-- A family of environments together with a prior weight on each.

`ι` is any index type -- naturals, bitstrings, anything. The weights must be
non-negative (automatic in `ℝ≥0∞`) and sum to at most one. -/
structure WeightedMixture (A E : Type*) [Fintype E] (ι : Type*) where
  /-- How much prior weight each environment receives. -/
  weight : ι → ℝ≥0∞
  /-- The environments being blended. -/
  env : ι → Environment A E
  /-- Total prior weight is at most one.

  Equality is deliberately not required: the Kraft inequality, which licenses
  complexity weights, gives only `≤ 1`. -/
  weight_le_one : ∑' i, weight i ≤ 1

namespace WeightedMixture

variable {ι : Type*}

/-- **The blend, as an environment in its own right.**

The probability it assigns to a percept is the weighted average of what each
ingredient environment assigns.

The semimeasure condition is inherited: total mass over percepts is at most the
total prior weight, which is at most one. The proof swaps the finite sum over
percepts with the infinite sum over environments, factors each weight out,
applies each ingredient's own bound, and then the weights' bound. -/
noncomputable def combine (M : WeightedMixture A E ι) : Environment A E where
  probability h a e := ∑' i, M.weight i * (M.env i).probability h a e
  totalProbabilityAtMostOne := by
    intro h a
    calc ∑ e : E, ∑' i, M.weight i * (M.env i).probability h a e
        = ∑' (e : E), ∑' i, M.weight i * (M.env i).probability h a e :=
          (tsum_fintype _).symm
      _ = ∑' i, ∑' (e : E), M.weight i * (M.env i).probability h a e :=
          ENNReal.tsum_comm
      _ = ∑' i, ∑ e : E, M.weight i * (M.env i).probability h a e :=
          tsum_congr fun i => tsum_fintype _
      _ = ∑' i, M.weight i * ∑ e : E, (M.env i).probability h a e :=
          tsum_congr fun i => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑' i, M.weight i * 1 := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          gcongr
          exact (M.env i).totalProbabilityAtMostOne h a
      _ = ∑' i, M.weight i := by simp
      _ ≤ 1 := M.weight_le_one

@[simp] theorem combine_probability (M : WeightedMixture A E ι) (h : History A E)
    (a : A) (e : E) :
    (M.combine).probability h a e
      = ∑' i, M.weight i * (M.env i).probability h a e := rfl

/-- **Domination.** The blend dominates each ingredient, scaled by that
ingredient's prior weight.

This is the property that makes blends useful. An environment with non-zero
prior weight is never assigned probability arbitrarily smaller than it assigns
itself -- the shortfall is bounded by a constant fixed in advance, independent
of how much interaction has occurred.

The proof is one line because it is just "a single term of a sum of non-negative
things is at most the whole sum". -/
theorem weight_mul_le_combine (M : WeightedMixture A E ι) (i : ι)
    (h : History A E) (a : A) (e : E) :
    M.weight i * (M.env i).probability h a e ≤ (M.combine).probability h a e :=
  ENNReal.le_tsum i

end WeightedMixture

end UAI
