/-
# Step 1a: Rewards

The very bottom of the development. This file answers one question:

> When the world sends the agent a message, how does the agent tell whether that
> message was good news or bad news?

Nothing here knows about time, environments, or agents. It is pure vocabulary.

## The one idea in this file

A **percept** is whatever the world sends the agent: a picture, a sentence, a
sensor reading. We never commit to what a percept *is*, because nothing in the
theory depends on that. We only require that a percept can be *scored*: given a
percept, there is a real number saying how good it was. That score is the
**reward**.

We keep the score *detachable* rather than gluing it into the percept type.
Concretely, we do not define

    Percept := Observation × Reward

Instead the percept type stays abstract and a scoring function is attached to it
separately. The reason is forward-looking: current research (Wyeth & Hutter,
*Value Under Ignorance in Universal Artificial Intelligence*, AGI 2025)
generalises AIXI away from "add up a per-step reward" toward scoring an entire
history at once. If reward were welded into the percept type, that change would
force rebuilding everything downstream. Because it is detachable, it does not.

Readers who want the textbook presentation `e = (o, r)` get it from the instance
below.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

namespace UAI

/-- `HasReward E` says: percepts of type `E` can be scored with a real number.

Read it as "this kind of message carries a score". The score may be any real
number; restrictions on its range are imposed separately, by
`RewardsInUnitInterval` below, and only on the theorems that need them. -/
class HasReward (E : Type*) where
  /-- The score carried by a percept. Higher is better. -/
  reward : E → ℝ

export HasReward (reward)

/-- The textbook percept type: a pair of (what you saw, how good it was).

Provided so a reader expecting the usual `e = (o, r)` presentation can have it.
Nothing in the development requires percepts to have this shape. -/
instance instHasRewardProd {O : Type*} : HasReward (O × ℝ) where
  reward := Prod.snd

/-- Scoring the textbook percept type just reads off the second component. -/
@[simp]
theorem reward_prod {O : Type*} (o : O) (r : ℝ) : reward (o, r) = r := rfl

/-- `RewardsInUnitInterval E` says every possible score lies between 0 and 1.

## Why this is a hypothesis and not a type

We could have made rewards live in a type containing only numbers between 0 and
1, making this true by construction. We deliberately did not.

1. Several theorems do not need it. Keeping it a hypothesis lets those theorems
   stay general, and lets Lean's linter *tell us* which ones do not need it --
   which is how we discovered that the attainment half of Bellman optimality
   requires no assumptions about rewards at all.

2. Someone may later want unbounded rewards (real-world losses are not capped at
   1). With boundedness as a hypothesis, that is a new theorem. With boundedness
   baked into the type, it would be a rewrite of the whole development.

## Why bounded at all

Because the agent adds up rewards over many steps. If single-step rewards could
be arbitrarily large, the total could be infinite, and "pick the action with the
highest total" would stop being a well-posed question. Bounding each step, plus
discounting the future, guarantees the total is finite. -/
def RewardsInUnitInterval (E : Type*) [HasReward E] : Prop :=
  ∀ e : E, 0 ≤ reward e ∧ reward e ≤ 1

/-- Extract the lower bound: scores are never negative. -/
theorem RewardsInUnitInterval.nonneg {E : Type*} [HasReward E]
    (hb : RewardsInUnitInterval E) (e : E) :
    0 ≤ reward e :=
  (hb e).1

/-- Extract the upper bound: scores never exceed 1. -/
theorem RewardsInUnitInterval.le_one {E : Type*} [HasReward E]
    (hb : RewardsInUnitInterval E) (e : E) :
    reward e ≤ 1 :=
  (hb e).2

end UAI
