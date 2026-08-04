/-
# Step 4: The universal prior — acting without knowing the environment

Blend all candidate environments into one, weighted by plausibility.

1. `Mixtures`          — a weighted blend of environments is an environment
2. `SimpleWeights`     — weights by list position (dependency-light)
3. `ComplexityWeights` — weights by Kolmogorov complexity (the real thing)
-/

import UAI.UniversalPrior.Mixtures
import UAI.UniversalPrior.SimpleWeights
import UAI.UniversalPrior.ComplexityWeights
