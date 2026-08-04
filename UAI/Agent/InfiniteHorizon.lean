/-
# Step 5b: AIXI

**This is the object the prose definition of AIXI describes.**

## The definition

    aixi  =  the policy that acts greedily with respect to
             the best achievable return over an unbounded future,
             computed against the complexity-weighted universal environment

In Lean, one line.

## How this differs from the bounded-horizon version

`aixiFinite` in the previous file is really a *family* of agents, one per
horizon: with `n` cycles remaining it maximises the `n`-step action-return, so
its behaviour at a given history depends on how much time is left. That is a
finite-horizon approximation.

`aixi` here maximises `returnOfActionForever`, which accounts for the entire
infinite future at once, via the Bellman fixed-point equation proved in
`Optimality/InfiniteHorizon.lean`. There is no horizon to be at.

## AIXI is stationary

`returnOfActionForever` carries no horizon argument, so `aixi` returns the same
action whenever the same history recurs. This is proved below by `rfl`.

Two consequences worth noting:

1. It recovers the standard fact that **discounted infinite-horizon problems
   admit stationary optimal policies**, here as an output of the construction
   rather than an assumption.

2. It means the infinite-horizon return theory of `Returns/InfiniteHorizon.lean`
   -- which is restricted to stationary policies, and where that restriction
   looked like a limitation -- applies to exactly this agent.

## Honest scope, again

Everything proved here is optimality **with respect to the universal
environment**. Since that environment is what defines the agent, these results
are close to true by construction. They do **not** say AIXI performs well
against the true environment.

That stronger claim is not proved here, and is known to fail in general: Leike &
Hutter, *Bad Universal Priors and Notions of Optimality* (COLT 2015), show that
adversarial choices of reference machine make AIXI misbehave drastically, and
that no invariance theorem is known for AIXI (unlike for Kolmogorov complexity
itself).
-/

import UAI.Optimality.InfiniteHorizon
import UAI.UniversalPrior.ComplexityWeights
import UAI.UniversalPrior.SimpleWeights

namespace UAI

variable {A E : Type*} [Fintype A] [Nonempty A] [Fintype E] [HasReward E]

section ComplexityWeighted

variable (U : Kolmogorov.Map) (hU : Kolmogorov.IsPrefixDecompressor U)
  (z : Kolmogorov.BitString) (env : Kolmogorov.BitString → Environment A E)

/-- **AIXI.** -/
noncomputable def aixi (γ : ℝ) : Policy A E :=
  bestPolicyForever (universalEnvironment U hU z env) γ

/-- The action AIXI takes at a history: the one maximising the unbounded-horizon
action-return. -/
@[simp] theorem aixi_apply (γ : ℝ) (n : ℕ) (h : History A E) :
    aixi U hU z env γ n h
      = bestActionForever (universalEnvironment U hU z env) γ h := rfl

/-- **AIXI is stationary**: the horizon argument is ignored entirely.

Proved by `rfl`, because `bestActionForever` simply has no horizon parameter to
depend on. -/
theorem aixi_stationary (γ : ℝ) (m n : ℕ) (h : History A E) :
    aixi U hU z env γ m h = aixi U hU z env γ n h := rfl

/-- **AIXI's action attains the best unbounded-horizon return.** -/
theorem returnOfActionForever_aixi {γ : ℝ} (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (h : History A E) :
    returnOfActionForever (universalEnvironment U hU z env) γ h
        (bestActionForever (universalEnvironment U hU z env) γ h)
      = bestReturnForever (universalEnvironment U hU z env) γ h :=
  returnOfActionForever_bestActionForever hb hγ hγ1 h

/-- **The Bellman fixed-point equation holds for AIXI's value function.**

This is the theorem that makes `aixi` a well-defined infinite-horizon object
rather than a limit of approximations. -/
theorem aixi_bellman {γ : ℝ} (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (hγ1 : γ < 1) (h : History A E) :
    bestReturnForever (universalEnvironment U hU z env) γ h
      = Finset.univ.sup' Finset.univ_nonempty
          (returnOfActionForever (universalEnvironment U hU z env) γ h) :=
  bestReturnForever_bellman hb hγ hγ1 h

/-- **No stationary policy beats AIXI's value** under the universal
environment. -/
theorem expectedReturnForever_le_aixi {γ : ℝ} (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (f : History A E → A) (h : History A E) :
    expectedReturnForever (universalEnvironment U hU z env) γ f h
      ≤ bestReturnForever (universalEnvironment U hU z env) γ h :=
  expectedReturnForever_le_bestReturnForever hb hγ hγ1 f h

/-- **AIXI's value is bounded** by the maximum return that is possible at all. -/
theorem bestReturnForever_aixi_le {γ : ℝ} (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (h : History A E) :
    bestReturnForever (universalEnvironment U hU z env) γ h
      ≤ maxPossibleReturn γ :=
  bestReturnForever_le_maxPossible hb hγ hγ1 h

/-- **The environment AIXI reasons with dominates every candidate**, scaled by
the complexity weight of that candidate's index.

Restated here for discoverability; the underlying fact is in
`UniversalPrior/ComplexityWeights.lean`.

Note carefully what this does *and does not* give: it bounds the shortfall in
**one-step probabilities**. Turning that into a bound on **returns** -- which is
what a genuine performance guarantee would require -- does not follow
discussed in the Roadmap in `README.md`. -/
theorem aixi_dominates (x : Kolmogorov.BitString) (h : History A E) (a : A)
    (e : E) :
    Kolmogorov.complexityWeight (Kolmogorov.KP U x z) * (env x).probability h a e
      ≤ (universalEnvironment U hU z env).probability h a e :=
  complexityWeight_mul_le_universal U hU z env x h a e

end ComplexityWeighted

section SimpleWeighted

/-- **AIXI with the position-weighted prior.** -/
noncomputable def aixiSimple (env : ℕ → Environment A E) (γ : ℝ) : Policy A E :=
  bestPolicyForever (simpleUniversalEnvironment env) γ

@[simp] theorem aixiSimple_apply (env : ℕ → Environment A E) (γ : ℝ) (n : ℕ)
    (h : History A E) :
    aixiSimple env γ n h
      = bestActionForever (simpleUniversalEnvironment env) γ h := rfl

theorem aixiSimple_stationary (env : ℕ → Environment A E) (γ : ℝ) (m n : ℕ)
    (h : History A E) :
    aixiSimple env γ m h = aixiSimple env γ n h := rfl

theorem aixiSimple_bellman (env : ℕ → Environment A E) {γ : ℝ}
    (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (h : History A E) :
    bestReturnForever (simpleUniversalEnvironment env) γ h
      = Finset.univ.sup' Finset.univ_nonempty
          (returnOfActionForever (simpleUniversalEnvironment env) γ h) :=
  bestReturnForever_bellman hb hγ hγ1 h

end SimpleWeighted

end UAI
