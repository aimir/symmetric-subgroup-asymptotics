import SymmetricSubgroupAsymptotics.ProductQuartetOddOrbitBound
import SymmetricSubgroupAsymptotics.ProductQuartetBinaryImageOrder
import SymmetricSubgroupAsymptotics.BinaryPairOddOrbitSectionBound

/-! A binary quotient of the original 32-point pair action has order at
most 2^15 whenever its actual sixteen-point top has a transitive quartet
frame with nonzero odd local kernel. Both factors use the SAME original N. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
open OriginalKernelModuleChart

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 16))
  (C : ProductBlockFrame F.top.range (Fin 4) Plane)

 theorem binary_quotient_card_le_fifteen
    [MulAction.IsPretransitive F.top.range (Fin 16)]
    (hO : oddKernel C.quartetLinearImage≠⊥)
    (N : Subgroup U) [N.Normal] (hQ : IsPGroup 2 (U ⧸ N)) :
    Nat.card (U ⧸ N)≤2^15 := by
  obtain ⟨P,hP,horbits⟩ := C.exists_odd_subgroup_eight_orbits hO
  let pi := F.top.rangeRestrict
  let R := U ⧸ (pi.ker ⊔ N)
  let phi := sectionTop pi N F.top.rangeRestrict_surjective
  have hphi : Function.Surjective phi := by
    intro r
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) r
    exact ⟨pi u,(sectionTop_apply pi N F.top.rangeRestrict_surjective u).trans hu⟩
  have hR : IsPGroup 2 R :=
    hQ.of_surjective (base pi N) (base_surjective pi N)
  have hresidual : Nat.card R≤2^7 := C.binary_image_card_le hO phi hphi hR
  exact F.binary_quotient_card_le_of_odd_orbits P hP 8 7 horbits N hQ hresidual

end SymmetricSubgroupAsymptotics.BinaryPairFrame
