import SymmetricSubgroupAsymptotics.BinaryPairIntervalPreimageNormalF
import SymmetricSubgroupAsymptotics.BinaryPairSmallInvariantLowerLayer
import SymmetricSubgroupAsymptotics.BinaryPairCentralDerivedFlip
import SymmetricSubgroupAsymptotics.BinaryPairAugmentationDerivedLift
import SymmetricSubgroupAsymptotics.BinaryPairIntervalPreimageGeometry
import SymmetricSubgroupAsymptotics.PGroupPermutationAugmentationExtension
import SymmetricSubgroupAsymptotics.BinaryPairAffineProperFCardPacket
import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule

/-! Proper normal F for the original augmentation-kernel degree32
source, for every SAME lower-dimensional original normal denominator.
The interval is chosen inside the actual lower augmentation; one selected
central derived lift is made pure, while all other offsets are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance augmentationSmallNormalFPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
    [MulAction.IsPretransitive U X]

theorem augmentation_small_axis_normalF_packet
    (hU : IsPGroup 2 U)
    (hK : F.kernelSpace=PermutationAugmentation.space (ZMod 2) (Fin 16))
    (hJ : 3≤Module.finrank (ZMod 2) E.kernelSpace)
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker)
    (hsmall : Module.finrank (ZMod 2) (F.ambientAxis N)≤3) :
    ∃ D : Subgroup (U ⧸ N),D.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog D+
        MarkedC4.ActualNormalFMarkedPeel.centralLog D≤16 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog D≤8 := by
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  letI : MulAction.IsPretransitive E.top.range (Fin 8) := E.top_pretransitive
  have hH := F.top_isPGroup hU
  let W := F.axisNaturalSubrepresentation N
  let A : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) E.top.range (Fin 8)) :=
    E.descendPairLayer (E.pairConstantModuleLayer W)
  have hWlower : W.toSubmodule≤E.pairSum.ker :=
    E.small_invariant_subrepresentation_le_pairSum_kernel hH 0 W (hsmall.trans hJ)
  have haxis : F.ambientAxis N=A.toSubmodule.map E.pairConstant := by
    apply le_antisymm
    · intro v hv
      have hm := hWlower hv
      obtain ⟨a,ha⟩ := E.pairConstant_pairSum_exact_linear.ge hm
      refine ⟨a,?_,ha⟩
      change E.pairConstant a=v at ha
      change E.pairConstant a ∈ W.toSubmodule
      rw [ha]
      exact hv
    · rintro _ ⟨a,ha,rfl⟩
      exact ha
  have hAdim : Module.finrank (ZMod 2) A.toSubmodule≤3 := by
    have hd := E.pairModuleLayers_finrank W
    change Module.finrank (ZMod 2) W.toSubmodule=
      Module.finrank (ZMod 2) (E.pairSumModuleLayer W).toSubmodule+
        Module.finrank (ZMod 2) A.toSubmodule at hd
    change Module.finrank (ZMod 2) W.toSubmodule≤3 at hsmall
    omega
  have hAproper : A.toSubmodule ≠ ⊤ := by
    intro he
    have hd := hAdim
    rw [he,finrank_top] at hd
    norm_num at hd
  have hAaug := pGroup_permutation_proper_subrepresentation_le_augmentation
    (E.top_isPGroup hH) (0 : Fin 8) A hAproper
  have hAlt : A.toSubmodule < PermutationAugmentation.space (ZMod 2) (Fin 8) := by
    apply lt_of_le_of_ne hAaug
    intro he
    have hd := PermutationAugmentation.space_finrank_add_one (k := ZMod 2) (0 : Fin 8)
    rw [←he] at hd
    norm_num only [Nat.card_fin] at hd
    omega
  let S : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) E.top.range (Fin 8)) :=
    permutationAugmentationSubrepresentation
  have hKS : F.kernelSpace=S.toSubmodule.comap E.pairSum := by
    rw [hK]
    ext v
    change PermutationAugmentation.coordinateSum (ZMod 2) (Fin 16) v=0 ↔
      PermutationAugmentation.coordinateSum (ZMod 2) (Fin 8) (E.pairSum v)=0
    rw [E.coordinateSum_eq_pairSum]
  obtain ⟨z,hzbits,hzcentral,hzderived⟩ :=
    E.exists_central_derived_constant_flip hH (0 : Fin 8) (by omega)
  have hp := F.interval_preimage_normalF_packet (w := 8) E hU (0 : Fin 8) A S hKS hAlt
    (by omega) z hzbits hzcentral
    (F.augmentation_affineClass_eq_zero_of_derived_top hK z.val hzderived) N hN haxis
  rcases hp with ⟨D,hD,hcost,hcenter⟩
  have hnum : (8 : ℝ)+(8 : ℝ)≤16 := by norm_num
  exact ⟨D,hD,hcost.trans hnum,hcenter⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
