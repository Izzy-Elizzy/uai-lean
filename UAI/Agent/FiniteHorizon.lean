/-
# Step 5a: AIXI over a bounded number of steps

## What AIXI is, in one sentence

Act greedily with respect to a universal environment.

That is the whole idea. Everything hard was done in the previous four steps:
`Optimality/` proved that acting greedily is optimal *for whatever environment
you are given*, and `UniversalPrior/` supplied an environment that is universal
for a family of candidates. AIXI is what you get by pointing the first at the
second.

## Why this file is almost empty

Every theorem below is an instantiation of a theorem proved elsewhere. Nothing
here requires an induction, a new hypothesis, or a new lemma. That the file is
short is the *point*: the content lives in the layers it composes, and keeping
them separate is what makes the composition trustworthy.

If you want to understand why AIXI is optimal, read
`Optimality/FiniteHorizon.lean`. If you want to understand what makes the
environment universal, read `UniversalPrior/ComplexityWeights.lean`. This file
just plugs them together.

## Two versions, and which is the "real" one

`aixiFinite` uses the **complexity-weighted** universal environment. This is the
prior the AIXI literature specifies, and it is the default.

`aixiFiniteSimple` uses the position-weighted one. Kept because it needs no
algorithmic-information machinery and because its universality theorem has no
side condition. See `UniversalPrior/SimpleWeights.lean`.

## Honest scope

"AIXI is optimal" here means optimal **with respect to the universal
environment** -- which, since that environment is what defines the agent, is
close to true by construction. It does *not* mean AIXI performs well against the
true environment; that claim is much stronger, is not proved here, and is known
to fail in general.
-/

import UAI.Optimality.FiniteHorizon
import UAI.UniversalPrior.ComplexityWeights
import UAI.UniversalPrior.SimpleWeights

namespace UAI

variable {A E : Type*} [Fintype A] [Nonempty A] [Fintype E] [HasReward E]

section ComplexityWeighted

variable (U : Kolmogorov.Map) (hU : Kolmogorov.IsPrefixDecompressor U)
  (z : Kolmogorov.BitString) (env : Kolmogorov.BitString → Environment A E)

/-- **AIXI over a bounded horizon.**

The policy that acts greedily with respect to the complexity-weighted universal
environment.

Non-stationary by construction: with `n + 1` cycles remaining it maximises the
`n`-step action-return, which generally differs from what it would choose at
another horizon. The unbounded-horizon version in `Agent/InfiniteHorizon.lean`
does not have this property. -/
noncomputable def aixiFinite (γ : ℝ) : Policy A E :=
  bestPolicy (universalEnvironment U hU z env) γ

@[simp] theorem aixiFinite_succ (γ : ℝ) (n : ℕ) (h : History A E) :
    aixiFinite U hU z env γ (n + 1) h
      = bestAction (universalEnvironment U hU z env) γ n h := rfl

/-- **AIXI attains the best achievable return** under the universal environment.

Unconditional -- no hypotheses on rewards or the discount. Inherited from
`expectedReturn_bestPolicy`; see there for why attainment needs nothing. -/
theorem expectedReturn_aixiFinite (γ : ℝ) (n : ℕ) (h : History A E) :
    expectedReturn (universalEnvironment U hU z env) γ
        (aixiFinite U hU z env γ) n h
      = bestReturn (universalEnvironment U hU z env) γ n h :=
  expectedReturn_bestPolicy n h

/-- **No policy beats AIXI** under the universal environment. -/
theorem expectedReturn_le_aixiFinite {γ : ℝ} (hγ : 0 ≤ γ) (π : Policy A E)
    (n : ℕ) (h : History A E) :
    expectedReturn (universalEnvironment U hU z env) γ π n h
      ≤ expectedReturn (universalEnvironment U hU z env) γ
          (aixiFinite U hU z env γ) n h := by
  rw [expectedReturn_aixiFinite]
  exact expectedReturn_le_bestReturn hγ π n h

/-- **AIXI's return cannot blow up.** -/
theorem expectedReturn_aixiFinite_le_geometricSum {γ : ℝ}
    (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ) (n : ℕ) (h : History A E) :
    expectedReturn (universalEnvironment U hU z env) γ
        (aixiFinite U hU z env γ) n h
      ≤ ∑ i ∈ Finset.range n, γ ^ i :=
  expectedReturn_le_geometricSum hb hγ n h

/-- **AIXI's return is never negative.** -/
theorem expectedReturn_aixiFinite_nonneg {γ : ℝ} (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (n : ℕ) (h : History A E) :
    0 ≤ expectedReturn (universalEnvironment U hU z env) γ
      (aixiFinite U hU z env γ) n h :=
  expectedReturn_nonneg hb hγ n h

/-- **AIXI is Bellman-optimal** under the universal environment: it attains the
best return, and no policy exceeds it. -/
theorem aixiFinite_isOptimal {γ : ℝ} (hγ : 0 ≤ γ) (n : ℕ) (h : History A E) :
    expectedReturn (universalEnvironment U hU z env) γ
          (aixiFinite U hU z env γ) n h
        = bestReturn (universalEnvironment U hU z env) γ n h ∧
      ∀ π : Policy A E,
        expectedReturn (universalEnvironment U hU z env) γ π n h
          ≤ expectedReturn (universalEnvironment U hU z env) γ
              (aixiFinite U hU z env γ) n h :=
  bestPolicy_isOptimal hγ n h

/-- **The environment AIXI reasons with dominates every candidate**, scaled by
the complexity weight of that candidate's index.

Restated here purely for discoverability -- a reader in `Agent/` should not have
to know this lives in `UniversalPrior/`. -/
theorem aixiFinite_dominates (x : Kolmogorov.BitString) (h : History A E)
    (a : A) (e : E) :
    Kolmogorov.complexityWeight (Kolmogorov.KP U x z) * (env x).probability h a e
      ≤ (universalEnvironment U hU z env).probability h a e :=
  complexityWeight_mul_le_universal U hU z env x h a e

end ComplexityWeighted

section SimpleWeighted

/-- **AIXI over a bounded horizon, with position-weighted prior.**

Same construction over `simpleUniversalEnvironment`. Retained as a
dependency-light alternative; see the file header. -/
noncomputable def aixiFiniteSimple (env : ℕ → Environment A E) (γ : ℝ) :
    Policy A E :=
  bestPolicy (simpleUniversalEnvironment env) γ

@[simp] theorem aixiFiniteSimple_succ (env : ℕ → Environment A E) (γ : ℝ)
    (n : ℕ) (h : History A E) :
    aixiFiniteSimple env γ (n + 1) h
      = bestAction (simpleUniversalEnvironment env) γ n h := rfl

theorem expectedReturn_aixiFiniteSimple (env : ℕ → Environment A E) (γ : ℝ)
    (n : ℕ) (h : History A E) :
    expectedReturn (simpleUniversalEnvironment env) γ
        (aixiFiniteSimple env γ) n h
      = bestReturn (simpleUniversalEnvironment env) γ n h :=
  expectedReturn_bestPolicy n h

theorem aixiFiniteSimple_isOptimal (env : ℕ → Environment A E) {γ : ℝ}
    (hγ : 0 ≤ γ) (n : ℕ) (h : History A E) :
    expectedReturn (simpleUniversalEnvironment env) γ
          (aixiFiniteSimple env γ) n h
        = bestReturn (simpleUniversalEnvironment env) γ n h ∧
      ∀ π : Policy A E,
        expectedReturn (simpleUniversalEnvironment env) γ π n h
          ≤ expectedReturn (simpleUniversalEnvironment env) γ
              (aixiFiniteSimple env γ) n h :=
  bestPolicy_isOptimal hγ n h

end SimpleWeighted

end UAI
