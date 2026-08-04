/-
# Step 4c: The universal environment (weights by Kolmogorov complexity)

## What this file does

The Solomonoff prior proper. Candidate environments are indexed by **bitstrings**
and weighted by `2^(-K(x))`, where `K` is prefix Kolmogorov complexity -- the
length of the shortest program producing `x`.

This is the weighting the AIXI literature specifies, and it is what
`Agent/` uses by default.

## Why complexity weighting is better than position weighting

Under `SimpleWeights.lean`, an environment's weight depends on where it happens
to sit in a list. Reorder the list and the agent's inductive bias changes, for
no principled reason.

Here, weight depends on the *complexity of the index*: shorter descriptions get
more mass. That is Occam's razor stated mathematically, and it is intrinsic --
no arbitrary ordering is involved. `simplerIndicesGetMoreWeight` below states
this directly.

## What makes it possible

The requirement `∑ weights ≤ 1` is exactly the **Kraft inequality** for prefix
complexity, available from the algorithmic-information library. Because
`Mixtures.lean` proved the blend theorem for abstract weights, supplying
complexity weights is a matter of discharging that single hypothesis --
everything else is inherited.

## One real difference from the simple version

Universality here carries a hypothesis that the simple version does not need:
the index must have *some* program (`K x z ≠ ⊤`). Since `complexityWeight ⊤ = 0`,
an index with no program receives zero weight and is not dominated at all.

That is not a defect. It is the honest complexity-theoretic behaviour showing up
in the type signature rather than being hidden.

## Honest scope

As in `SimpleWeights.lean`: the family of candidate environments is an **input**,
not constructed here. Constructing an actual enumeration of the
lower-semicomputable chronological semimeasures is genuine computability theory
and is not attempted anywhere in this development.
-/

import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyTest
import UAI.UniversalPrior.Mixtures

namespace UAI

open scoped ENNReal

variable {A E : Type*} [Fintype E]

/-- The blend weighting each candidate by `2^(-K(x | z))`.

`U` is the reference prefix machine (complexity is only defined relative to a
machine) and `z` is a condition string. Subnormalization is the Kraft
inequality. -/
noncomputable def complexityMixture (U : Kolmogorov.Map)
    (hU : Kolmogorov.IsPrefixDecompressor U) (z : Kolmogorov.BitString)
    (env : Kolmogorov.BitString → Environment A E) :
    WeightedMixture A E Kolmogorov.BitString where
  weight x := Kolmogorov.complexityWeight (Kolmogorov.KP U x z)
  env := env
  weight_le_one := Kolmogorov.KP_kraft_sum_le_one U hU z

/-- **The universal environment**, written `ξ` in the literature.

This is the default universal environment of this development. -/
noncomputable def universalEnvironment (U : Kolmogorov.Map)
    (hU : Kolmogorov.IsPrefixDecompressor U) (z : Kolmogorov.BitString)
    (env : Kolmogorov.BitString → Environment A E) : Environment A E :=
  (complexityMixture U hU z env).combine

@[simp] theorem universalEnvironment_probability (U : Kolmogorov.Map)
    (hU : Kolmogorov.IsPrefixDecompressor U) (z : Kolmogorov.BitString)
    (env : Kolmogorov.BitString → Environment A E) (h : History A E) (a : A)
    (e : E) :
    (universalEnvironment U hU z env).probability h a e
      = ∑' x : Kolmogorov.BitString,
          Kolmogorov.complexityWeight (Kolmogorov.KP U x z)
            * (env x).probability h a e :=
  rfl

/-- **Domination.** The universal environment dominates each candidate, scaled
by `2^(-K(x))`.

The scaling factor depends on the *complexity* of the index rather than its
position: an environment with a short description is dominated with a large
constant. -/
theorem complexityWeight_mul_le_universal (U : Kolmogorov.Map)
    (hU : Kolmogorov.IsPrefixDecompressor U) (z : Kolmogorov.BitString)
    (env : Kolmogorov.BitString → Environment A E) (x : Kolmogorov.BitString)
    (h : History A E) (a : A) (e : E) :
    Kolmogorov.complexityWeight (Kolmogorov.KP U x z) * (env x).probability h a e
      ≤ (universalEnvironment U hU z env).probability h a e :=
  (complexityMixture U hU z env).weight_mul_le_combine x h a e

/-- **Universality, with a complexity-derived constant.**

For every candidate whose index has *some* program, there is a strictly positive
constant -- determined by that index's complexity -- by which the universal
environment dominates it, uniformly over all histories, actions and percepts.

The hypothesis `K x z ≠ ⊤` is not bookkeeping: `complexityWeight ⊤ = 0`, so an
index with no program receives zero weight and genuinely is not dominated. -/
theorem universalEnvironment_universal (U : Kolmogorov.Map)
    (hU : Kolmogorov.IsPrefixDecompressor U) (z : Kolmogorov.BitString)
    (env : Kolmogorov.BitString → Environment A E) (x : Kolmogorov.BitString)
    (hx : Kolmogorov.KP U x z ≠ ⊤) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧
      ∀ (h : History A E) (a : A) (e : E),
        c * (env x).probability h a e
          ≤ (universalEnvironment U hU z env).probability h a e :=
  ⟨Kolmogorov.complexityWeight (Kolmogorov.KP U x z),
    (Kolmogorov.complexityWeight_pos_iff _).mpr hx,
    Kolmogorov.complexityWeight_ne_top _,
    complexityWeight_mul_le_universal U hU z env x⟩

/-- **Occam's razor, stated directly.** An index that is no more complex than
another receives at least as much weight.

This is the property the positional weighting of `SimpleWeights.lean`
fundamentally cannot express, and it is the whole point of preferring complexity
weights. -/
theorem simplerIndicesGetMoreWeight (U : Kolmogorov.Map)
    (z : Kolmogorov.BitString) {x y : Kolmogorov.BitString}
    (hxy : Kolmogorov.KP U x z ≤ Kolmogorov.KP U y z) :
    Kolmogorov.complexityWeight (Kolmogorov.KP U y z)
      ≤ Kolmogorov.complexityWeight (Kolmogorov.KP U x z) :=
  Kolmogorov.complexityWeight_antitone hxy

end UAI
