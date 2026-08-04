/-
# Step 2: Returns — how well a given policy does

Given a policy and an environment, what total discounted reward should we
expect? Answered first for a bounded number of steps, then in the limit.

1. `FiniteHorizon`   — expected return with `n` steps remaining
2. `InfiniteHorizon` — the limit as `n` grows, for stationary policies
-/

import UAI.Returns.FiniteHorizon
import UAI.Returns.InfiniteHorizon
