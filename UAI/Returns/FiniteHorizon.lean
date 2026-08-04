/-
# Step 2a: Expected return over a bounded number of steps

The first file that computes something rather than just naming things.

## The question

If the agent follows policy `π` in environment `ν`, starting from history `h`,
with `n` interaction cycles left to go -- what total reward should it expect?

## The answer, in words

With zero steps left, nothing more happens, so the expected total is zero.

With `n + 1` steps left: the agent takes the action its policy prescribes. The
environment then replies with some percept -- we do not know which, so we
average over all of them, weighting each by how likely the environment says it
is. For each possible percept, the agent collects that percept's reward now, and
then faces the same problem again from the extended history with `n` steps left.
Future reward is discounted by a factor `γ`, so reward `k` steps away is worth
`γ^k` times face value.

## Discounting, and why

`γ` (gamma) is between 0 and 1. It encodes "a reward now is worth more than the
same reward later". It is not just a modelling preference: it is what keeps
infinite totals finite. Without it, `Returns/InfiniteHorizon.lean` could not
exist.

## The mixed number types, and why they are mixed

Probabilities live in `ℝ≥0∞`; rewards and returns live in plain `ℝ`. These
cannot be multiplied directly, so probabilities are converted down with
`probabilityReal`.

Why not put everything in `ℝ≥0∞`? Because `ℝ≥0∞` subtraction is *truncated*:
`3 - 5 = 0` rather than `-2`. Any theorem comparing two returns by subtracting
them would silently get wrong answers. Returns must therefore be ordinary reals.

Why not put everything in `ℝ`? Because infinite sums of ordinary reals need
convergence side conditions everywhere, which `UniversalPrior/Mixtures.lean`
would drown in.

So the split is deliberate, and the conversion is sound precisely because of
`Environment.probability_ne_top`: without it, `⊤` would silently convert to `0`
and quietly corrupt every computation.
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import UAI.Setup.Environments
import UAI.Setup.Policies

namespace UAI

open scoped ENNReal BigOperators

variable {A E : Type*} [Fintype E] [HasReward E]

/-- An environment's probability, converted from `ℝ≥0∞` to an ordinary real.

Sound because `Environment.probability_ne_top` guarantees the value is never
infinite. (`ENNReal.toReal` sends `⊤` to `0`, so without that guarantee this
conversion would silently lose information.) -/
noncomputable def Environment.probabilityReal
    (ν : Environment A E) (h : History A E) (a : A) (e : E) : ℝ :=
  (ν.probability h a e).toReal

namespace Environment

omit [HasReward E] in
/-- Converted probabilities are still non-negative. -/
theorem probabilityReal_nonneg (ν : Environment A E) (h : History A E) (a : A)
    (e : E) :
    0 ≤ ν.probabilityReal h a e :=
  ENNReal.toReal_nonneg

omit [HasReward E] in
/-- Converted probabilities are still at most one. -/
theorem probabilityReal_le_one (ν : Environment A E) (h : History A E) (a : A)
    (e : E) :
    ν.probabilityReal h a e ≤ 1 := by
  have h1 : ν.probability h a e ≤ 1 := ν.probability_le_one h a e
  have h2 : ν.probability h a e ≠ ⊤ := ν.probability_ne_top h a e
  rw [Environment.probabilityReal, ← ENNReal.toReal_one]
  gcongr
  exact ENNReal.one_ne_top

omit [HasReward E] in
/-- Converted probabilities still sum to at most one.

This is `totalProbabilityAtMostOne` carried across the conversion. It is not
automatic -- converting each term separately and then summing could in principle
differ from converting the sum -- which is why it needs `probability_ne_top` for
every term. It is used at the key step of every bound in this file. -/
theorem sum_probabilityReal_le_one (ν : Environment A E) (h : History A E)
    (a : A) :
    ∑ e : E, ν.probabilityReal h a e ≤ 1 := by
  have hne : ∀ e ∈ (Finset.univ : Finset E), ν.probability h a e ≠ ⊤ :=
    fun e _ => ν.probability_ne_top h a e
  have hsum : (∑ e : E, ν.probability h a e).toReal
      = ∑ e : E, (ν.probability h a e).toReal :=
    ENNReal.toReal_sum hne
  have hne_top : (∑ e : E, ν.probability h a e) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (ν.totalProbabilityAtMostOne h a)
  have hle : (∑ e : E, ν.probability h a e).toReal ≤ (1 : ℝ≥0∞).toReal :=
    (ENNReal.toReal_le_toReal hne_top ENNReal.one_ne_top).mpr
      (ν.totalProbabilityAtMostOne h a)
  simpa [Environment.probabilityReal, hsum] using hle

end Environment

/-- **Expected return over a bounded horizon.**

`expectedReturn ν γ π n h` is the total discounted reward the agent should
expect, starting from history `h`, following policy `π`, in environment `ν`,
with `n` interaction cycles remaining.

The policy is consulted at the *current* remaining horizon: with `n + 1` cycles
left, the agent acts as `π (n + 1) h`. Notice that this action appears twice in
the recursive case -- once selecting which row of the environment's distribution
we draw from, and once inside the extended history passed to the recursive call.
That second occurrence is the source of every difficulty in this theory: the
agent's choices do not merely get scored, they become part of the input to
everything that follows. -/
noncomputable def expectedReturn (ν : Environment A E) (γ : ℝ) (π : Policy A E) :
    ℕ → History A E → ℝ
  | 0, _ => 0
  | n + 1, h =>
      ∑ e : E, ν.probabilityReal h (π (n + 1) h) e *
        (reward e + γ * expectedReturn ν γ π n (h.extend (π (n + 1) h) e))

/-- With no steps remaining, nothing more can happen, so the expected return is
zero. -/
@[simp] theorem expectedReturn_zero (ν : Environment A E) (γ : ℝ)
    (π : Policy A E) (h : History A E) :
    expectedReturn ν γ π 0 h = 0 := rfl

/-- The recursive step, stated as a rewritable equation.

True by definition; stated separately so proofs can `rw` with it instead of
unfolding. -/
theorem expectedReturn_succ (ν : Environment A E) (γ : ℝ) (π : Policy A E)
    (n : ℕ) (h : History A E) :
    expectedReturn ν γ π (n + 1) h
      = ∑ e : E, ν.probabilityReal h (π (n + 1) h) e *
          (reward e + γ * expectedReturn ν γ π n (h.extend (π (n + 1) h) e)) :=
  rfl

section Bounds

variable {ν : Environment A E} {γ : ℝ} {π : Policy A E}

/-- **Expected return is never negative**, given non-negative rewards and a
non-negative discount.

Obvious, but worth having proved: it is the first confirmation that the
recursion composes correctly rather than producing nonsense.

Proof idea: induct on the horizon. Each term of the sum is a product of
non-negative things. -/
theorem expectedReturn_nonneg (hb : RewardsInUnitInterval E) (hγ : 0 ≤ γ) :
    ∀ (n : ℕ) (h : History A E), 0 ≤ expectedReturn ν γ π n h := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
      intro h
      rw [expectedReturn_succ]
      refine Finset.sum_nonneg ?_
      intro e _
      have hp : 0 ≤ ν.probabilityReal h (π (n + 1) h) e :=
        ν.probabilityReal_nonneg h (π (n + 1) h) e
      have hr : 0 ≤ reward e := hb.nonneg e
      have hv : 0 ≤ expectedReturn ν γ π n (h.extend (π (n + 1) h) e) := ih _
      have hsum :
          0 ≤ reward e + γ * expectedReturn ν γ π n (h.extend (π (n + 1) h) e) :=
        add_nonneg hr (mul_nonneg hγ hv)
      exact mul_nonneg hp hsum

/-- **Expected return cannot exceed the geometric sum** `1 + γ + γ² + ... + γⁿ⁻¹`.

This is the theorem that stops returns from blowing up. It says: no matter what
the agent does or what environment it is in, with `n` steps left it cannot
expect more than it would get from a perfect reward of 1 at every step.

Proof idea (induction on the horizon). Each reward is at most 1, and each
continuation return is at most the `n`-step bound by the induction hypothesis;
so each term of the sum is bounded. Sum the bounds, factor out the constant, and
apply `sum_probabilityReal_le_one` -- this is the step where the semimeasure
property does its work. Finally `geom_sum_succ` recognises the result as the
`(n+1)`-term geometric sum.

The cleaner-looking bound `1 / (1 - γ)` needs `γ < 1` and appears in
`Returns/InfiniteHorizon.lean`, where it is the statement that actually
matters. -/
theorem expectedReturn_le_geometricSum (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) :
    ∀ (n : ℕ) (h : History A E),
      expectedReturn ν γ π n h ≤ ∑ i ∈ Finset.range n, γ ^ i := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
      intro h
      have hS : (0 : ℝ) ≤ ∑ i ∈ Finset.range n, γ ^ i :=
        Finset.sum_nonneg fun i _ => pow_nonneg hγ i
      have hbound : (0 : ℝ) ≤ γ * (∑ i ∈ Finset.range n, γ ^ i) + 1 := by
        have hmul : (0 : ℝ) ≤ γ * ∑ i ∈ Finset.range n, γ ^ i := mul_nonneg hγ hS
        linarith
      have hterm : ∀ e ∈ (Finset.univ : Finset E),
          ν.probabilityReal h (π (n + 1) h) e *
              (reward e
                + γ * expectedReturn ν γ π n (h.extend (π (n + 1) h) e))
            ≤ ν.probabilityReal h (π (n + 1) h) e *
              (γ * (∑ i ∈ Finset.range n, γ ^ i) + 1) := by
        intro e _
        refine mul_le_mul_of_nonneg_left ?_
          (ν.probabilityReal_nonneg h (π (n + 1) h) e)
        have hr : reward e ≤ 1 := hb.le_one e
        have hv : γ * expectedReturn ν γ π n (h.extend (π (n + 1) h) e)
            ≤ γ * ∑ i ∈ Finset.range n, γ ^ i :=
          mul_le_mul_of_nonneg_left (ih _) hγ
        linarith
      calc expectedReturn ν γ π (n + 1) h
          = ∑ e : E, ν.probabilityReal h (π (n + 1) h) e *
              (reward e
                + γ * expectedReturn ν γ π n (h.extend (π (n + 1) h) e)) := rfl
        _ ≤ ∑ e : E, ν.probabilityReal h (π (n + 1) h) e *
              (γ * (∑ i ∈ Finset.range n, γ ^ i) + 1) := Finset.sum_le_sum hterm
        _ = (∑ e : E, ν.probabilityReal h (π (n + 1) h) e) *
              (γ * (∑ i ∈ Finset.range n, γ ^ i) + 1) := by
              rw [← Finset.sum_mul]
        _ ≤ 1 * (γ * (∑ i ∈ Finset.range n, γ ^ i) + 1) :=
              mul_le_mul_of_nonneg_right
                (ν.sum_probabilityReal_le_one h (π (n + 1) h)) hbound
        _ = γ * (∑ i ∈ Finset.range n, γ ^ i) + 1 := one_mul _
        _ = ∑ i ∈ Finset.range (n + 1), γ ^ i := geom_sum_succ.symm

end Bounds

section Stationary

variable {ν : Environment A E} {γ : ℝ}

/-- **More time is never worse -- but only for stationary policies.**

## Why the restriction is necessary, not lazy

For a general policy this statement is **false**, and it is worth understanding
why, because the reason recurs throughout this development.

`expectedReturn ν γ π n h` consults `π` at horizon `n`, while
`expectedReturn ν γ π (n+1) h` consults it at horizon `n+1`. Those may be
completely different actions. A policy that behaves sensibly with five steps
left but throws the game with six left violates the inequality outright. The
theorem is not hard to prove for such policies; it is simply wrong.

For a stationary policy the horizon argument is ignored, both sides take the
same action, and the comparison goes through termwise.

## What this means downstream

The monotonicity that matters for optimality is monotonicity of the *best
possible* return, not of a fixed policy's return -- and that version *is* true
in general, because at each horizon the best return maximises afresh rather than
committing to a possibly-erratic policy. See
`bestReturn_mono_horizon` in `Optimality/InfiniteHorizon.lean`. -/
theorem expectedReturn_mono_horizon_of_stationary (hb : RewardsInUnitInterval E)
    (hγ : 0 ≤ γ) (f : History A E → A) :
    ∀ (n : ℕ) (h : History A E),
      expectedReturn ν γ (Policy.ofStationary f) n h
        ≤ expectedReturn ν γ (Policy.ofStationary f) (n + 1) h := by
  intro n
  induction n with
  | zero =>
      intro h
      rw [expectedReturn_zero]
      exact expectedReturn_nonneg (π := Policy.ofStationary f) hb hγ 1 h
  | succ n ih =>
      intro h
      rw [expectedReturn_succ, expectedReturn_succ]
      simp only [Policy.ofStationary_apply]
      refine Finset.sum_le_sum ?_
      intro e _
      refine mul_le_mul_of_nonneg_left ?_ (ν.probabilityReal_nonneg h (f h) e)
      have hstep :
          γ * expectedReturn ν γ (Policy.ofStationary f) n (h.extend (f h) e)
            ≤ γ * expectedReturn ν γ (Policy.ofStationary f) (n + 1)
                (h.extend (f h) e) :=
        mul_le_mul_of_nonneg_left (ih _) hγ
      linarith

end Stationary

end UAI
