import SymmetricSubgroupAsymptotics.BinaryNormalFTheorem57Proof
import SymmetricSubgroupAsymptotics.MarkedC4PublishedSevenTargets
import SymmetricSubgroupAsymptotics.Targets

/-!
# Public entry point for symmetric subgroup asymptotics

The final proof facade imports the approved definitions, all required finite
certificates and structural proofs, and the analytic transfers from T1 to T2
and T3. Its T1 and AllTargets exports take the explicitly named published
inputs documented in `formal/README.md`. The shared-threshold reformulations
from Section 5 of the specification are also exported here.

Optional regression fixtures and alternative certificates remain available
through their own module imports.
-/
import SymmetricSubgroupAsymptotics.CFSGJankoTwoDihedralT1Reduction
import SymmetricSubgroupAsymptotics.TraceyExceptionalMersenneDegreeArithmetic
import SymmetricSubgroupAsymptotics.CFSGSolubleSylowNormalizerT1Reduction
import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalProjectiveEquivalence
