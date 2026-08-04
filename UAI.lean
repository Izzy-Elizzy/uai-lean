/-
# Universal Artificial Intelligence, formalised in Lean 4

A machine-checked construction of AIXI: from the agent-environment interaction
protocol, through value functions and Bellman optimality, to the universal
environment and the agent itself.

Everything is `sorry`-free. See `README.md` for what is and is not claimed.

## Reading order

    Setup           →  Returns  →  Optimality  →  UniversalPrior  →  Agent
    (vocabulary)       (how well    (how well      (acting without    (AIXI)
                        a policy     is it          knowing the
                        does)        possible       environment)
                                     to do)
-/

import UAI.Setup
import UAI.Returns
import UAI.Optimality
import UAI.UniversalPrior
import UAI.Agent
