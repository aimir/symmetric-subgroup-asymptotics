import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNonzeroOddQuotientSocles
import SymmetricSubgroupAsymptotics.SocleGeneratorCharacterInterval

/-! Actual nonzero-odd A4/S4 quartet frames give a retained character interval:
all original axes below the odd preimage have whole-socle bound2, while
all axes above it are charged once to the faithful8 binary comparator.
No binary quotient socle bound is asserted or required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingNonzeroOddIntervalData
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneWreathActualOddKernel

def data (U : Subgroup (Equiv.Perm (Fin 16)))
    (C : Subgroup Frame)
    (hO : oddKernel C≠⊥)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (pi : U →* C) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) C) [FiniteDimensional (ZMod 2) A]
    (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
    (hj : Function.Injective j)
 : SocleGeneratorCharacterIntervalData U where
  E := BinaryPlaneAlternatingRetainedComparator.retained C pi
  quotientDegree := 8
  quotientAction := BinaryPlaneAlternatingRetainedComparator.quotientAction C pi
  quotientAction_injective := BinaryPlaneAlternatingRetainedComparator.quotientAction_injective C pi
  slots := 2
  quotientSocleGenerators N hnot := by
    letI := N.property
    exact BinaryPlaneAlternatingNonzeroOddQuotientSocles.quotientSocle C hO heven pi hpi A E j hj N.val

end SymmetricSubgroupAsymptotics.SixteenPointSemanticAlternatingNonzeroOddIntervalData
