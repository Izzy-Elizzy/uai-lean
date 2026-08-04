/-
# Step 3a: The best achievable return, and the policy achieving it

The previous step asked "how well does *this* policy do?". This step asks "how
well is it possible to do at all, and what does one have to do to achieve it?"

## The two objects

* `bestReturn ν γ n h` -- the highest expected return achievable from history
  `h` with `n` cycles remaining, over *all* policies.
* `returnOfAction ν γ n h a` -- the return from taking action `a` right now and
  then continuing optimally. Called the "Q function" in reinforcement learning.

They are related by the **Bellman equation**: the best you can do is to take the
best available action, so `bestReturn` at `n+1` is the maximum of
`returnOfAction` over all actions.

## The two halves of optimality, deliberately separated

Optimality is really two claims, and they have very different characters:

* **Soundness** -- no policy does better than `bestReturn`.
  Requires only `0 ≤ γ`. Interestingly, it does *not* require bounded rewards:
  the reward term appears identically on both sides of the comparison and
  cancels, so only the sign of the discount matters.

* **Attainment** -- the greedy policy achieves `bestReturn` exactly.
  Requires **nothing at all**. This surprises people, so it is worth saying
  plainly: `bestReturn` is *defined* as the maximum over actions, and
  `bestAction` *selects* a maximiser. Attainment is therefore true by
  construction, in the same way that "the tallest person in the room is at least
  as tall as everyone in the room" is true without knowing anyone's height. No
  reasoning about magnitudes occurs, so no assumptions about magnitudes are
  needed.

We found these minimal hypotheses by writing the proofs and letting Lean's
linter report which assumptions went unused. That is a small but real example of
formalisation producing a sharper result than the informal version.

## Why the action set must be finite and non-empty

`bestReturn` maximises over actions. A maximum over an infinite set need not
exist, and a maximum over an empty set certainly does not. Hence
`[Fintype A]` and `[Nonempty A]`, which appear here for the first time.
-/

import UAI.Returns.FiniteHorizon

namespace UAI

open scoped BigOperators

variable {A E : Type*} [Fintype A] [Nonempty A] [Fintype E] [HasReward E]

/-- **The best achievable expected return** from history `h` with `n` cycles
remaining.

At each step it takes the maximum over available actions, rather than following
any fixed policy. That distinction matters later: because it re-maximises at
every horizon rather than committing, it behaves better than a fixed policy's
return does (see `bestReturn_mono_horizon`). -/
noncomputable def bestReturn (ν : Environment A E) (γ : ℝ) :
    ℕ → History A E → ℝ
  | 0, _ => 0
  | n + 1, h =>
      Finset.univ.sup' Finset.univ_nonempty fun a =>
        ∑ e : E, ν.probabilityReal h a e *
          (reward e + γ * bestReturn ν γ n (h.extend a e))

/-- **The return from taking a specific action now, then continuing optimally.**

Known in the reinforcement-learning literature as the *Q function*. Splitting it
out from `bestReturn` lets the Bellman equation be stated as "the best return is
the best action-return", which is both clearer and easier to work with. -/
noncomputable def returnOfAction (ν : Environment A E) (γ : ℝ) (n : ℕ)
    (h : History A E) (a : A) : ℝ :=
  ∑ e : E, ν.probabilityReal h a e *
    (reward e + γ * bestReturn ν γ n (h.extend a e))

/-- With no steps remaining, the best achievable return is zero. -/
@[simp] theorem bestReturn_zero (ν : Environment A E) (γ : ℝ)
    (h : History A E) :
    bestReturn ν γ 0 h = 0 := rfl

/-- **The Bellman equation (bounded horizon).** The best return is the best
action-return.

True by definition; stated separately so it can be used as a rewrite and so the
Bellman equation is findable by name. -/
theorem bestReturn_succ (ν : Environment A E) (γ : ℝ) (n : ℕ)
    (h : History A E) :
    bestReturn ν γ (n + 1) h
      = Finset.univ.sup' Finset.univ_nonempty (returnOfAction ν γ n h) := rfl

/-- No single action beats the best over all actions. Immediate from the Bellman
equation. -/
theorem returnOfAction_le_bestReturn (ν : Environment A E) (γ : ℝ) (n : ℕ)
    (h : History A E) (a : A) :
    returnOfAction ν γ n h a ≤ bestReturn ν γ (n + 1) h := by
  rw [bestReturn_succ]
  exact Finset.le_sup' (returnOfAction ν γ n h) (Finset.mem_univ a)

section Soundness

variable {ν : Environment A E} {γ : ℝ}

/-- **Soundness: no policy achieves more than `bestReturn`.**

Requires only `0 ≤ γ`. Bounded rewards are *not* needed: the reward term appears
identically on both sides of the comparison and cancels, so only the sign of the
discount matters.

Proof idea: induct on the horizon. Replace the policy's continuation return by
the best continuation return (that is the induction hypothesis), which can only
increase each term; the result is the action-return of whatever action the
policy chose, which is at most the maximum over actions. -/
theorem expectedReturn_le_bestReturn (hγ : 0 ≤ γ) (π : Policy A E) :
    ∀ (n : ℕ) (h : History A E),
      expectedReturn ν γ π n h ≤ bestReturn ν γ n h := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
      intro h
      have hterm : ∀ e ∈ (Finset.univ : Finset E),
          ν.probabilityReal h (π (n + 1) h) e *
              (reward e
                + γ * expectedReturn ν γ π n (h.extend (π (n + 1) h) e))
            ≤ ν.probabilityReal h (π (n + 1) h) e *
              (reward e
                + γ * bestReturn ν γ n (h.extend (π (n + 1) h) e)) := by
        intro e _
        refine mul_le_mul_of_nonneg_left ?_
          (ν.probabilityReal_nonneg h (π (n + 1) h) e)
        have := mul_le_mul_of_nonneg_left (ih (h.extend (π (n + 1) h) e)) hγ
        linarith
      calc expectedReturn ν γ π (n + 1) h
          = ∑ e : E, ν.probabilityReal h (π (n + 1) h) e *
              (reward e
                + γ * expectedReturn ν γ π n (h.extend (π (n + 1) h) e)) := rfl
        _ ≤ ∑ e : E, ν.probabilityReal h (π (n + 1) h) e *
              (reward e
                + γ * bestReturn ν γ n (h.extend (π (n + 1) h) e)) :=
              Finset.sum_le_sum hterm
        _ = returnOfAction ν γ n h (π (n + 1) h) := rfl
        _ ≤ bestReturn ν γ (n + 1) h :=
              returnOfAction_le_bestReturn ν γ n h (π (n + 1) h)

end Soundness

section Greedy

variable (ν : Environment A E) (γ : ℝ)

/-- **An action maximising the action-return** at horizon `n` and history `h`.

Chosen classically from the finitely many available actions. No tie-breaking
rule is imposed: when several actions are equally good, which one is picked is
unspecified, and none of the results below depend on the choice. -/
noncomputable def bestAction (n : ℕ) (h : History A E) : A :=
  (Finset.exists_max_image Finset.univ (returnOfAction ν γ n h)
    Finset.univ_nonempty).choose

/-- `bestAction` really is a maximiser: no action beats it. -/
theorem bestAction_max (n : ℕ) (h : History A E) (a : A) :
    returnOfAction ν γ n h a ≤ returnOfAction ν γ n h (bestAction ν γ n h) :=
  (Finset.exists_max_image Finset.univ (returnOfAction ν γ n h)
    Finset.univ_nonempty).choose_spec.2 a (Finset.mem_univ a)

/-- The greedy action achieves the best return exactly. -/
theorem returnOfAction_bestAction (n : ℕ) (h : History A E) :
    returnOfAction ν γ n h (bestAction ν γ n h) = bestReturn ν γ (n + 1) h := by
  refine le_antisymm (returnOfAction_le_bestReturn ν γ n h _) ?_
  rw [bestReturn_succ]
  exact Finset.sup'_le _ _ fun a _ => bestAction_max ν γ n h a

/-- **The greedy policy**: with `n + 1` cycles remaining, take an action
maximising the action-return.

Note this is genuinely non-stationary -- the action depends on `n`. This is
exactly why `Policy` was defined to take a horizon argument; under a
history-only definition this policy could not be written down.

At horizon `0` nothing further happens, so the action is irrelevant and is
chosen arbitrarily. -/
noncomputable def bestPolicy : Policy A E
  | 0, _ => Classical.arbitrary A
  | n + 1, h => bestAction ν γ n h

@[simp] theorem bestPolicy_succ (n : ℕ) (h : History A E) :
    bestPolicy ν γ (n + 1) h = bestAction ν γ n h := rfl

end Greedy

section Attainment

variable {ν : Environment A E} {γ : ℝ}

/-- **Attainment: the greedy policy achieves the best return exactly.**

**Unconditional** -- no hypotheses on rewards or on the discount. See the file
header for why: `bestReturn` is defined as a maximum and `bestAction` selects a
maximiser, so this is true by construction rather than by any argument about
magnitudes. -/
theorem expectedReturn_bestPolicy :
    ∀ (n : ℕ) (h : History A E),
      expectedReturn ν γ (bestPolicy ν γ) n h = bestReturn ν γ n h := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
      intro h
      rw [expectedReturn_succ, bestPolicy_succ]
      have hcongr : ∀ e ∈ (Finset.univ : Finset E),
          ν.probabilityReal h (bestAction ν γ n h) e *
              (reward e + γ * expectedReturn ν γ (bestPolicy ν γ) n
                (h.extend (bestAction ν γ n h) e))
            = ν.probabilityReal h (bestAction ν γ n h) e *
              (reward e + γ * bestReturn ν γ n
                (h.extend (bestAction ν γ n h) e)) := by
        intro e _
        rw [ih (h.extend (bestAction ν γ n h) e)]
      rw [Finset.sum_congr rfl hcongr]
      exact returnOfAction_bestAction ν γ n h

/-- **Bellman optimality**: the greedy policy attains the best return, and no
policy exceeds it.

The two halves combined. Requires only `0 ≤ γ`, inherited entirely from the
soundness half; attainment contributes no hypotheses. -/
theorem bestPolicy_isOptimal (hγ : 0 ≤ γ) (n : ℕ) (h : History A E) :
    expectedReturn ν γ (bestPolicy ν γ) n h = bestReturn ν γ n h ∧
      ∀ π : Policy A E,
        expectedReturn ν γ π n h ≤ expectedReturn ν γ (bestPolicy ν γ) n h := by
  refine ⟨expectedReturn_bestPolicy n h, fun π => ?_⟩
  rw [expectedReturn_bestPolicy n h]
  exact expectedReturn_le_bestReturn hγ π n h

end Attainment

end UAI
