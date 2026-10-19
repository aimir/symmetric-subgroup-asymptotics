import SymmetricSubgroupAsymptotics.BinaryPlaneKleinRetainedQuotientSocles
import SymmetricSubgroupAsymptotics.SocleGeneratorCharacterInterval

/-! Actual sixteen-point V4 frames give a retained character interval:
all original axes below the odd preimage have whole-socle bound2, while
all axes above it are charged once to the faithful8 binary comparator.
No binary quotient socle bound is asserted or required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticKleinIntervalData
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
abbrev R := BinaryRegularKleinWreath.R
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

def data (U : Subgroup (Equiv.Perm (Fin 16)))
    (C : Subgroup (W (R := R) (I := R)))
    (pi : U →* C) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) C) [FiniteDimensional (ZMod 2) A]
    (E : OriginalKernelModuleChart pi A)
    (j : Representation.IntertwiningMap A.ρ (BinaryPlaneKleinUniform.representation C))
    (hj : Function.Injective j)
    (hblocks : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := R) →* R).comp C.subtype))
    (hU : ¬ IsPGroup 2 U) : SocleGeneratorCharacterIntervalData U where
  E := BinaryPlaneKleinRetainedComparator.retained C pi
  quotientDegree := 8
  quotientAction := BinaryPlaneKleinRetainedComparator.quotientAction C pi
  quotientAction_injective := BinaryPlaneKleinRetainedComparator.quotientAction_injective C pi
  slots := 2
  quotientSocleGenerators N hnot := by
    letI := N.property
    apply BinaryPlaneKleinRetainedQuotientSocles.quotientSocle C pi hpi A E j hj hblocks hU N.val
    simpa only [BinaryPlaneKleinRetainedComparator.retained_eq_preimage] using hnot

end SymmetricSubgroupAsymptotics.SixteenPointSemanticKleinIntervalData
