/-
# Step 3b: The best achievable return over an unbounded future

## The headline

The best achievable return, over an infinite future, satisfies the **Bellman
fixed-point equation**:

    bestReturnForever h  =  max over actions a of
        ∑ over percepts e of  ν(e | h, a) * (reward e + γ * bestReturnForever (h·ae))

This is the equation that defines what AIXI *is*, in the prose sense. It has no
base case and no counting down: the value at a history is defined in terms of
the value at the next histories, all at once.

## Why we did not need the Banach fixed-point theorem

The textbook route to a fixed-point value function is: set up the bounded
functions `History → ℝ` as a complete metric space, prove the Bellman operator
is a `γ`-contraction on it, and apply Banach. That is real machinery.

None of it is needed here, because of one observation:

> `bestReturn ν γ n h` is **monotone** in `n`.

Compare `expectedReturn_mono_horizon_of_stationary`, where monotonicity had to
be restricted to stationary policies because a fixed erratic policy can behave
worse with more time. `bestReturn` has no such problem: it does not follow a
fixed policy at all, it re-maximises over actions at every horizon, so more
horizon can only help.

Monotone plus bounded gives convergence, exactly as in `Returns/`. The fixed
point then falls out of a limit-interchange argument (below) rather than a
contraction argument.

## The limit interchange, in words

The Bellman equation is proved by two inequalities.

**Easy direction (`≤`).** Every bounded-horizon best return is a maximum over
actions of `returnOfAction`, and each of those is at most the corresponding
unbounded-horizon action-return, because `bestReturn n ≤ bestReturnForever`
pointwise. Take the supremum over `n`. Pure monotonicity, no limits.

**Hard direction (`≥`).** Fix an action `a`. Rather than chase epsilons:

1. `bestReturn n (h·ae)` converges to `bestReturnForever (h·ae)` -- proved in
   this file.
2. Finite sums and multiplication by constants are continuous, so
   `returnOfAction n h a` converges to `returnOfActionForever h a`.
3. But every term satisfies `returnOfAction n h a ≤ bestReturnForever h`.
4. A convergent sequence bounded above by a constant has its limit bounded by
   that constant. So `returnOfActionForever h a ≤ bestReturnForever h`.
5. True for every action, hence for the maximum.

Step 4 is why no epsilon argument appears anywhere.
-/

import UAI.Returns.InfiniteHorizon
import UAI.Optimality.FiniteHorizon

namespace UAI

open scoped BigOperators
open Filter Topology

variable {A E : Type*} [Fintype A] [Nonempty A] [Fintype E] [HasReward E]

section Bounds

variable {ν : Environment A E} {γ : ℝ}

/-- The best return is bounded by the geometric sum, exactly as any single
policy's return is.

Proved directly rather than deduced from `expectedReturn_le_geometricSum`,
because the best return is a maximisation and not the return of any one fixed
policy. The proof is structurally the same induction. -/
theorem bestReturn_le_geometricSum (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ) :
    ∀ (n : ℕ) (h : History A E),
      bestReturn ν γ n h ≤ ∑ i ∈ Finset.range n, γ ^ i := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
      intro h
      rw [bestReturn_succ]
      refine Finset.sup'_le _ _ fun a _ => ?_
      have hS : (0 : ℝ) ≤ ∑ i ∈ Finset.range n, γ ^ i :=
        Finset.sum_nonneg fun i _ => pow_nonneg hγ i
      have hbound : (0 : ℝ) ≤ γ * (∑ i ∈ Finset.range n, γ ^ i) + 1 := by
        have hmul : (0 : ℝ) ≤ γ * ∑ i ∈ Finset.range n, γ ^ i := mul_nonneg hγ hS
        linarith
      have hterm : ∀ e ∈ (Finset.univ : Finset E),
          ν.probabilityReal h a e
              * (reward e + γ * bestReturn ν γ n (h.extend a e))
            ≤ ν.probabilityReal h a e
              * (γ * (∑ i ∈ Finset.range n, γ ^ i) + 1) := by
        intro e _
        refine mul_le_mul_of_nonneg_left ?_ (ν.probabilityReal_nonneg h a e)
        have hr : reward e ≤ 1 := hb.le_one e
        have hv : γ * bestReturn ν γ n (h.extend a e)
            ≤ γ * ∑ i ∈ Finset.range n, γ ^ i :=
          mul_le_mul_of_nonneg_left (ih _) hγ
        linarith
      calc returnOfAction ν γ n h a
          = ∑ e : E, ν.probabilityReal h a e *
              (reward e + γ * bestReturn ν γ n (h.extend a e)) := rfl
        _ ≤ ∑ e : E, ν.probabilityReal h a e *
              (γ * (∑ i ∈ Finset.range n, γ ^ i) + 1) := Finset.sum_le_sum hterm
        _ = (∑ e : E, ν.probabilityReal h a e) *
              (γ * (∑ i ∈ Finset.range n, γ ^ i) + 1) := by rw [← Finset.sum_mul]
        _ ≤ 1 * (γ * (∑ i ∈ Finset.range n, γ ^ i) + 1) :=
              mul_le_mul_of_nonneg_right
                (ν.sum_probabilityReal_le_one h a) hbound
        _ = γ * (∑ i ∈ Finset.range n, γ ^ i) + 1 := one_mul _
        _ = ∑ i ∈ Finset.range (n + 1), γ ^ i := geom_sum_succ.symm

/-- The best return is bounded uniformly in the horizon. -/
theorem bestReturn_le_maxPossible (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (hγ1 : γ < 1) (n : ℕ) (h : History A E) :
    bestReturn ν γ n h ≤ maxPossibleReturn γ := by
  have hsummable : Summable fun i : ℕ => γ ^ i :=
    summable_geometric_of_lt_one hγ hγ1
  have hpartial : ∑ i ∈ Finset.range n, γ ^ i ≤ ∑' i : ℕ, γ ^ i :=
    hsummable.sum_le_tsum _ (fun i _ => pow_nonneg hγ i)
  calc bestReturn ν γ n h ≤ ∑ i ∈ Finset.range n, γ ^ i :=
        bestReturn_le_geometricSum hb hγ n h
    _ ≤ ∑' i : ℕ, γ ^ i := hpartial
    _ = maxPossibleReturn γ := tsum_geometric_of_lt_one hγ hγ1

/-- The best return is never negative.

Proved by comparison with a concrete policy: the constant policy achieves a
non-negative return, and the best return is at least what any policy
achieves. -/
theorem bestReturn_nonneg (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ) :
    ∀ (n : ℕ) (h : History A E), 0 ≤ bestReturn ν γ n h := by
  intro n h
  cases n with
  | zero => simp
  | succ m =>
      have h1 : (0 : ℝ)
          ≤ expectedReturn ν γ (Policy.const (Classical.arbitrary A)) (m + 1) h :=
        expectedReturn_nonneg hb hγ (m + 1) h
      have h2 : expectedReturn ν γ (Policy.const (Classical.arbitrary A))
            (m + 1) h ≤ bestReturn ν γ (m + 1) h :=
        expectedReturn_le_bestReturn hγ
          (Policy.const (Classical.arbitrary A)) (m + 1) h
      linarith

/-- **The best return is monotone in the horizon.**

This is the key fact that makes the whole infinite-horizon development possible
without a contraction argument, and it is worth contrasting with
`expectedReturn_mono_horizon_of_stationary`, which had to be restricted.

The value of a *fixed* policy need not be monotone, because a non-stationary
policy may behave differently -- possibly worse -- when given more time. The
*best* value has no such problem: at each horizon it maximises afresh, so
additional horizon can only expand the set of achievable outcomes. -/
theorem bestReturn_mono_horizon (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ) :
    ∀ (n : ℕ) (h : History A E),
      bestReturn ν γ n h ≤ bestReturn ν γ (n + 1) h := by
  intro n
  induction n with
  | zero =>
      intro h
      rw [bestReturn_zero]
      exact bestReturn_nonneg hb hγ 1 h
  | succ n ih =>
      intro h
      rw [bestReturn_succ, bestReturn_succ]
      refine Finset.sup'_le _ _ fun a _ => ?_
      refine le_trans ?_
        (Finset.le_sup' (returnOfAction ν γ (n + 1) h) (Finset.mem_univ a))
      refine Finset.sum_le_sum fun e _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (ν.probabilityReal_nonneg h a e)
      have hstep : γ * bestReturn ν γ n (h.extend a e)
          ≤ γ * bestReturn ν γ (n + 1) (h.extend a e) :=
        mul_le_mul_of_nonneg_left (ih _) hγ
      linarith

end Bounds

section Unbounded

variable {ν : Environment A E} {γ : ℝ}

/-- The bounded-horizon best returns, viewed as a sequence in the horizon. -/
noncomputable def bestReturnSeq (ν : Environment A E) (γ : ℝ)
    (h : History A E) : ℕ → ℝ :=
  fun n => bestReturn ν γ n h

theorem bestReturnSeq_monotone (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (h : History A E) :
    Monotone (bestReturnSeq ν γ h) :=
  monotone_nat_of_le_succ fun n => bestReturn_mono_horizon hb hγ n h

theorem bestReturnSeq_bddAbove (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (hγ1 : γ < 1) (h : History A E) :
    BddAbove (Set.range (bestReturnSeq ν γ h)) := by
  refine ⟨maxPossibleReturn γ, ?_⟩
  rintro x ⟨n, rfl⟩
  exact bestReturn_le_maxPossible hb hγ hγ1 n h

/-- **The best achievable return over an unbounded future.**

This is the value function AIXI maximises. -/
noncomputable def bestReturnForever (ν : Environment A E) (γ : ℝ)
    (h : History A E) : ℝ :=
  ⨆ n : ℕ, bestReturnSeq ν γ h n

theorem bestReturn_le_forever (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (hγ1 : γ < 1) (n : ℕ) (h : History A E) :
    bestReturn ν γ n h ≤ bestReturnForever ν γ h :=
  le_ciSup (bestReturnSeq_bddAbove hb hγ hγ1 h) n

theorem bestReturnForever_le_maxPossible (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (h : History A E) :
    bestReturnForever ν γ h ≤ maxPossibleReturn γ :=
  ciSup_le fun n => bestReturn_le_maxPossible hb hγ hγ1 n h

/-- **The bounded-horizon best returns converge to the unbounded one.** -/
theorem tendsto_bestReturnForever (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (hγ1 : γ < 1) (h : History A E) :
    Tendsto (bestReturnSeq ν γ h) atTop (𝓝 (bestReturnForever ν γ h)) :=
  tendsto_atTop_ciSup (bestReturnSeq_monotone hb hγ h)
    (bestReturnSeq_bddAbove hb hγ hγ1 h)

/-- **Soundness (unbounded horizon)**: no stationary policy beats the best
return. -/
theorem expectedReturnForever_le_bestReturnForever (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (f : History A E → A) (h : History A E) :
    expectedReturnForever ν γ f h ≤ bestReturnForever ν γ h := by
  refine ciSup_le fun n => ?_
  refine le_trans
    (expectedReturn_le_bestReturn hγ (Policy.ofStationary f) n h) ?_
  exact bestReturn_le_forever hb hγ hγ1 n h

end Unbounded

section BellmanEquation

variable {ν : Environment A E} {γ : ℝ}

/-- **The unbounded-horizon action-return**: take action `a` now, then continue
optimally forever. -/
noncomputable def returnOfActionForever (ν : Environment A E) (γ : ℝ)
    (h : History A E) (a : A) : ℝ :=
  ∑ e : E, ν.probabilityReal h a e *
    (reward e + γ * bestReturnForever ν γ (h.extend a e))

theorem bestReturnForever_nonneg (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (hγ1 : γ < 1) (h : History A E) :
    0 ≤ bestReturnForever ν γ h := by
  refine le_trans ?_ (bestReturn_le_forever hb hγ hγ1 0 h)
  simp

theorem returnOfActionForever_nonneg (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (hγ1 : γ < 1) (h : History A E) (a : A) :
    0 ≤ returnOfActionForever ν γ h a := by
  refine Finset.sum_nonneg fun e _ => ?_
  refine mul_nonneg (ν.probabilityReal_nonneg h a e) ?_
  have hr : 0 ≤ reward e := hb.nonneg e
  have hv : 0 ≤ γ * bestReturnForever ν γ (h.extend a e) :=
    mul_nonneg hγ (bestReturnForever_nonneg hb hγ hγ1 (h.extend a e))
  linarith

/-- **Step 2 of the interchange**: the bounded-horizon action-returns converge to
the unbounded one.

Built from continuity: finite sums are continuous, multiplication by a constant
is continuous, and the inner best returns converge by
`tendsto_bestReturnForever`. -/
theorem tendsto_returnOfActionForever (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (h : History A E) (a : A) :
    Tendsto (fun n => returnOfAction ν γ n h a) atTop
      (𝓝 (returnOfActionForever ν γ h a)) := by
  refine tendsto_finsetSum _ fun e _ => ?_
  refine Tendsto.const_mul _ ?_
  refine Tendsto.const_add _ ?_
  exact (tendsto_bestReturnForever hb hγ hγ1 (h.extend a e)).const_mul γ

/-- **Step 3 of the interchange**: every bounded-horizon action-return is
bounded by the unbounded-horizon best return. -/
theorem returnOfAction_le_bestReturnForever (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (n : ℕ) (h : History A E) (a : A) :
    returnOfAction ν γ n h a ≤ bestReturnForever ν γ h :=
  le_trans (returnOfAction_le_bestReturn ν γ n h a)
    (bestReturn_le_forever hb hγ hγ1 (n + 1) h)

/-- **Step 4 of the interchange**: therefore the *limit* is bounded by it too.

This is where the limit interchange actually happens, and `le_of_tendsto` is
what makes it an argument about convergence rather than an epsilon chase. -/
theorem returnOfActionForever_le_bestReturnForever (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (h : History A E) (a : A) :
    returnOfActionForever ν γ h a ≤ bestReturnForever ν γ h :=
  le_of_tendsto (tendsto_returnOfActionForever hb hγ hγ1 h a)
    (Eventually.of_forall fun n =>
      returnOfAction_le_bestReturnForever hb hγ hγ1 n h a)

/-- Bounded-horizon action-returns are below unbounded ones, pointwise. -/
theorem returnOfAction_le_forever (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (hγ1 : γ < 1) (n : ℕ) (h : History A E) (a : A) :
    returnOfAction ν γ n h a ≤ returnOfActionForever ν γ h a := by
  refine Finset.sum_le_sum fun e _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (ν.probabilityReal_nonneg h a e)
  have hstep : γ * bestReturn ν γ n (h.extend a e)
      ≤ γ * bestReturnForever ν γ (h.extend a e) :=
    mul_le_mul_of_nonneg_left
      (bestReturn_le_forever hb hγ hγ1 n (h.extend a e)) hγ
  linarith

/-- **THE BELLMAN FIXED-POINT EQUATION.**

    bestReturnForever h  =  max over actions of  returnOfActionForever h

`bestReturnForever` is a fixed point of the Bellman operator: its value at a
history is the best available action-return, where the action-returns are
themselves computed against `bestReturnForever`.

This is the central theorem of the development. It is what makes it possible to
define an infinite-horizon optimal policy at all: without a fixed-point
equation, there is nothing to be greedy with respect to.

See the file header for the two directions of the proof. -/
theorem bestReturnForever_bellman (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ)
    (hγ1 : γ < 1) (h : History A E) :
    bestReturnForever ν γ h
      = Finset.univ.sup' Finset.univ_nonempty
          (returnOfActionForever ν γ h) := by
  refine le_antisymm ?_ ?_
  · -- Easy direction: pure monotonicity, no limits.
    refine ciSup_le fun n => ?_
    cases n with
    | zero =>
        change bestReturn ν γ 0 h ≤ _
        rw [bestReturn_zero]
        have h1 : (0 : ℝ)
            ≤ returnOfActionForever ν γ h (Classical.arbitrary A) :=
          returnOfActionForever_nonneg hb hγ hγ1 h (Classical.arbitrary A)
        have h2 : returnOfActionForever ν γ h (Classical.arbitrary A)
            ≤ Finset.univ.sup' Finset.univ_nonempty
                (returnOfActionForever ν γ h) :=
          Finset.le_sup' (returnOfActionForever ν γ h) (Finset.mem_univ _)
        linarith
    | succ m =>
        change bestReturn ν γ (m + 1) h ≤ _
        rw [bestReturn_succ]
        refine Finset.sup'_le _ _ fun a _ => ?_
        have h1 : returnOfAction ν γ m h a ≤ returnOfActionForever ν γ h a :=
          returnOfAction_le_forever hb hγ hγ1 m h a
        have h2 : returnOfActionForever ν γ h a
            ≤ Finset.univ.sup' Finset.univ_nonempty
                (returnOfActionForever ν γ h) :=
          Finset.le_sup' (returnOfActionForever ν γ h) (Finset.mem_univ a)
        linarith
  · -- Hard direction: the limit interchange.
    refine Finset.sup'_le _ _ fun a _ => ?_
    exact returnOfActionForever_le_bestReturnForever hb hγ hγ1 h a

end BellmanEquation

section BestPolicyForever

variable (ν : Environment A E) (γ : ℝ)

/-- An action maximising the unbounded-horizon action-return. -/
noncomputable def bestActionForever (h : History A E) : A :=
  (Finset.exists_max_image Finset.univ (returnOfActionForever ν γ h)
    Finset.univ_nonempty).choose

theorem bestActionForever_max (h : History A E) (a : A) :
    returnOfActionForever ν γ h a
      ≤ returnOfActionForever ν γ h (bestActionForever ν γ h) :=
  (Finset.exists_max_image Finset.univ (returnOfActionForever ν γ h)
    Finset.univ_nonempty).choose_spec.2 a (Finset.mem_univ a)

/-- **The unbounded-horizon optimal policy.**

**It is stationary**: `returnOfActionForever` carries no horizon argument, so
the same history always yields the same action.

This recovers the standard fact that discounted infinite-horizon problems admit
stationary optimal policies -- and it means the results of
`Returns/InfiniteHorizon.lean`, which are restricted to stationary policies,
apply to exactly this agent. The restriction that looked like a compromise turns
out to be exactly the right scope. -/
noncomputable def bestPolicyForever : Policy A E :=
  Policy.ofStationary (bestActionForever ν γ)

@[simp] theorem bestPolicyForever_apply (n : ℕ) (h : History A E) :
    bestPolicyForever ν γ n h = bestActionForever ν γ h := rfl

end BestPolicyForever

section ForeverAttainment

variable {ν : Environment A E} {γ : ℝ}

/-- **Attainment (unbounded horizon)**: the greedy action achieves the best
unbounded-horizon return. -/
theorem returnOfActionForever_bestActionForever (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (h : History A E) :
    returnOfActionForever ν γ h (bestActionForever ν γ h)
      = bestReturnForever ν γ h := by
  refine le_antisymm
    (returnOfActionForever_le_bestReturnForever hb hγ hγ1 h _) ?_
  rw [bestReturnForever_bellman hb hγ hγ1 h]
  exact Finset.sup'_le _ _ fun a _ => bestActionForever_max ν γ h a

end ForeverAttainment

end UAI
