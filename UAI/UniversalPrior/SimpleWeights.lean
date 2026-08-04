/-
# Step 4b: The simple universal environment (weights by list position)

## What this file does

Takes a list of candidate environments and blends them, weighting the `i`-th one
by `2^-(i+1)`. Those weights are positive and sum to exactly one, so
`Mixtures.lean` immediately gives a valid environment that dominates every
candidate.

## Where this sits relative to the "real" universal prior

This is the **simpler of the two** universal environments in this development.
Its weights depend only on an environment's *position in a list*, not on
anything about the environment itself. Reordering the list changes which
environments are favoured, which is philosophically unsatisfying: there is no
principled reason position 3 should be more plausible than position 40.

`ComplexityWeights.lean` fixes exactly that, weighting by Kolmogorov complexity
so that *simplicity* -- an intrinsic property -- determines plausibility. That is
the version the AIXI literature specifies, and it is the default used by
`Agent/`.

## Why this file is kept anyway

Two honest reasons.

1. **It is more general in one respect.** Under complexity weighting, an index
   with no program at all receives weight zero and is not dominated. Here every
   index receives strictly positive weight, with no exceptions.

2. **It has no external dependencies beyond a weight sequence**, so it remains
   usable by anyone who does not want to pull in an algorithmic-information
   library.

## Honest scope

The list of candidate environments is an **input**, not something constructed
here. Actually enumerating the lower-semicomputable environments is genuine
computability theory and is not attempted anywhere in this development. Every
result below is relative to whatever list is supplied: the blend is universal
*for the family it is given*.
-/

import KolmogorovMathlib.AlgorithmicProbability.UniversalMixture
import UAI.UniversalPrior.Mixtures

namespace UAI

open scoped ENNReal

variable {A E : Type*} [Fintype E]

/-- The blend that weights the `i`-th candidate environment by `2^-(i+1)`.

The weights come from the algorithmic-information library rather than being
redefined here. They are a bare sequence of numbers with no dependence on
bitstrings or machines, so no encoding of histories is needed at this layer.

Subnormalization is discharged by `tsum_dyadicWeight`, which gives equality with
one; we weaken it to `≤ 1`. -/
noncomputable def simpleMixture (env : ℕ → Environment A E) :
    WeightedMixture A E ℕ where
  weight := Kolmogorov.dyadicWeight
  env := env
  weight_le_one := Kolmogorov.tsum_dyadicWeight.le

/-- **The simple universal environment**, written `ξ` in the literature.

Universal for the supplied list of candidates, in the sense of
`simpleUniversalEnvironment_universal` below. -/
noncomputable def simpleUniversalEnvironment (env : ℕ → Environment A E) :
    Environment A E :=
  (simpleMixture env).combine

@[simp] theorem simpleUniversalEnvironment_probability
    (env : ℕ → Environment A E) (h : History A E) (a : A) (e : E) :
    (simpleUniversalEnvironment env).probability h a e
      = ∑' i, Kolmogorov.dyadicWeight i * (env i).probability h a e := rfl

/-- **Domination.** The simple universal environment dominates every candidate,
scaled by that candidate's positional weight. -/
theorem weight_mul_le_simpleUniversal (env : ℕ → Environment A E) (i : ℕ)
    (h : History A E) (a : A) (e : E) :
    Kolmogorov.dyadicWeight i * (env i).probability h a e
      ≤ (simpleUniversalEnvironment env).probability h a e :=
  (simpleMixture env).weight_mul_le_combine i h a e

/-- **Universality.** For *every* candidate there is a strictly positive, finite
constant by which the blend dominates it -- uniformly over all histories,
actions and percepts.

Note the absence of any hypothesis: unlike the complexity-weighted version,
every index here qualifies. This is the one respect in which the simple version
is more general.

Why this matters: it says predictions made under the blend can be worse than
predictions made under the truth by at most a factor fixed *in advance*,
independent of how long the interaction runs. -/
theorem simpleUniversalEnvironment_universal (env : ℕ → Environment A E)
    (i : ℕ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧
      ∀ (h : History A E) (a : A) (e : E),
        c * (env i).probability h a e
          ≤ (simpleUniversalEnvironment env).probability h a e :=
  ⟨Kolmogorov.dyadicWeight i, Kolmogorov.dyadicWeight_pos i,
    Kolmogorov.dyadicWeight_ne_top i, weight_mul_le_simpleUniversal env i⟩

end UAI
