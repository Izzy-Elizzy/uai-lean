/-
# Step 1: Setup — the vocabulary

Actions, percepts, rewards, histories, policies, environments.

Nothing in this layer mentions value, optimality, or AIXI. It defines the pieces
everything else is built from, and it depends on nothing in this project.

Read in this order:
1. `Rewards`      — how percepts are scored
2. `Histories`    — the record of what has happened
3. `Policies`     — what an agent is
4. `Environments` — what the world is
-/

import UAI.Setup.Rewards
import UAI.Setup.Histories
import UAI.Setup.Policies
import UAI.Setup.Environments
