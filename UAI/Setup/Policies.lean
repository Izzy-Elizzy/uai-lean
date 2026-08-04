/-
# Step 1c: Policies

What an agent *is*, mechanically.

## The definition

A policy is a rule that answers: "given everything that has happened, and given
how much time is left, what do I do next?"

    Policy A E := ℕ → History A E → A

The `ℕ` is the number of interaction cycles **remaining**, not elapsed.

## Why the horizon argument is there

The best action often depends on how much time is left. With ten rounds
remaining you might invest and build an advantage. With one round remaining you
should grab whatever reward is available right now, because there is no future
to invest in. Same history, different correct action, purely because the clock
differs.

A policy that saw only the history could not express that, and so could not
express the optimal finite-horizon policies the theory is about. This is not a
hypothetical concern: the greedy policy constructed in
`Optimality/FiniteHorizon.lean` is genuinely non-stationary, and under a
history-only definition it would be inexpressible.

## Why "remaining" rather than "elapsed"

Both conventions can express the same policies. Counting down matches the
recursion in `Returns/FiniteHorizon.lean`, which peels off one step at a time
from a remaining budget. Using the same convention in both places means the two
never need reconciling arithmetic.

## Two deliberate restrictions

* **Deterministic.** A policy returns an action, not a distribution over
  actions. For the finite-horizon results, an optimal deterministic policy
  always exists (the action set is finite), so nothing is lost. Stochastic
  policies, if ever wanted, would be a new type rather than a revision of this
  one.

* **Total.** A policy is defined at every horizon and every history, including
  histories its own past choices make unreachable. This is standard and avoids
  carrying reachability side conditions through every proof.
-/

import UAI.Setup.Histories

namespace UAI

/-- A deterministic policy: the action taken when `n` cycles remain and history
`h` has occurred. -/
abbrev Policy (A E : Type*) := ℕ → History A E → A

namespace Policy

variable {A E : Type*}

/-- The policy that always takes the same action, whatever has happened and
however much time is left.

Included as the simplest possible witness that `Policy` is a usable, non-empty
definition rather than a well-typed shell. -/
def const (a : A) : Policy A E := fun _ _ => a

@[simp] theorem const_apply (a : A) (n : ℕ) (h : History A E) :
    const a n h = a := rfl

/-- A **stationary** policy: one whose action depends on the history but not on
how much time is left.

This is a genuinely important special case, not a convenience. Several results
are true only for stationary policies -- see
`expectedReturn_mono_horizon_of_stationary` -- and, pleasingly, the
*infinite*-horizon optimal policy turns out to be stationary
(`Agent/InfiniteHorizon.lean`), so those restricted results apply to it. -/
def ofStationary (f : History A E → A) : Policy A E := fun _ h => f h

@[simp] theorem ofStationary_apply (f : History A E → A) (n : ℕ)
    (h : History A E) :
    ofStationary f n h = f h := rfl

/-- Policies exist whenever actions do. -/
instance [Inhabited A] : Inhabited (Policy A E) := ⟨const default⟩

end Policy

end UAI
