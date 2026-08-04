/-
# Step 1b: Histories

The record of everything that has happened.

## The interaction protocol

Agent and environment take strict turns forever:

    agent:         a₁      a₂      a₃   ...
                     ↘   ↗   ↘   ↗   ↘
    environment:       e₁      e₂      e₃  ...

The agent emits an **action**; the environment replies with a **percept**;
repeat. A **history** is the record of that alternation: `a₁ e₁ a₂ e₂ a₃ e₃ ...`

## Why this is the right level of generality

Notice what this protocol does *not* assume. There is no state space, no Markov
property, no assumption that the environment is stationary or even nicely
probabilistic. The environment may depend on the *entire* past in arbitrarily
complicated ways.

Contrast standard reinforcement learning, which usually assumes a Markov
Decision Process: states, with transition probabilities depending only on the
current state. AIXI throws that away. This protocol is the weakest possible
interface between an agent and a world, and that weakness is exactly what makes
the resulting theory general.

## Representation choice

A history is a single list of `(action, percept)` pairs, not two synchronised
lists. Two lists would require carrying an invariant ("they always have the same
length") and proving it preserved by every operation. Pairing makes the
invariant impossible to violate, so it never needs stating.

We use `abbrev` rather than `def` so that Lean's entire `List` library applies
to histories directly, without unfolding anything.
-/

import UAI.Setup.Rewards

namespace UAI

/-- A history: the alternating record of actions taken and percepts received.

`A` is the type of actions the agent can take, `E` the type of percepts the
environment can send. -/
abbrev History (A E : Type*) := List (A × E)

namespace History

variable {A E : Type*}

/-- The empty history: nothing has happened yet. -/
def empty : History A E := []

/-- Extend a history by one action-percept pair.

`h.extend a e` is "history `h` happened, then the agent did `a`, then the world
replied `e`". This is the operation the value recursion uses to step forward in
time. -/
def extend (h : History A E) (a : A) (e : E) : History A E := h ++ [(a, e)]

@[simp] theorem empty_eq_nil : (empty : History A E) = [] := rfl

@[simp] theorem length_empty : (empty : History A E).length = 0 := rfl

/-- Extending a history makes it exactly one step longer. -/
@[simp] theorem length_extend (h : History A E) (a : A) (e : E) :
    (h.extend a e).length = h.length + 1 := by
  simp [extend]

/-- An extended history is never the empty one: something has happened. -/
@[simp] theorem extend_ne_empty (h : History A E) (a : A) (e : E) :
    h.extend a e ≠ empty := by
  simp [extend, empty]

/-- How many complete interaction cycles have occurred.

Since each list entry is one full action-percept exchange, the length of the
history *is* the elapsed time. -/
abbrev time (h : History A E) : ℕ := h.length

end History

end UAI
