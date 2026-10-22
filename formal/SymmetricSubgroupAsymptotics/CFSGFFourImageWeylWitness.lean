import SymmetricSubgroupAsymptotics.CFSGFFourImageWeylAction
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootFixed
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEvenOrder

/-! Noncentrality in the SAME original F4 source-image group is witnessed
on the image of its actual E_2 generator. This works in characteristic two
as well and does not require a scalar natural commutant. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGSerreModelRootGeneration
local instance fFourImageWeylWitnessDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
variable (K : Type) [Field K]

theorem imageWeyl_not_center : imageWeyl K∉Subgroup.center (imageGroup K) := by
  intro hc
  let R := modelRoot CartanMatrix.F₄ K false 2 1
  let y : (baseChange realizationData K).range := (baseChange realizationData K).rangeRestrict
    (1⊗ₜ[ℤ]CFSGSerreDiagram.latticeGenerator CartanMatrix.F₄ (CartanMatrix.Generators.E 2))
  have hy : y.val=fieldRoot realizationData K false 2 := by
    change baseChange realizationData K
      (1⊗ₜ[ℤ]CFSGSerreDiagram.latticeGenerator CartanMatrix.F₄ (CartanMatrix.Generators.E 2))=_
    rw [baseChange_generator]
    rfl
  have hRfix : imageRepresentation realizationData K R y=y := by
    apply Subtype.ext
    rw [long_root_image_action,hy]
    exact canonicalRoot_fixes_root realizationData K false 2 1
  have hWy : (imageRepresentation realizationData K (sourceWeyl K) y).val=
      (canonicalWeyl realizationData K 2 : Matrix Index Index K)*fieldRoot realizationData K false 2*
        (↑((canonicalWeyl realizationData K 2)⁻¹):Matrix Index Index K) := by
    rw [weyl_image_action,hy]
  have hcomm := (Subgroup.mem_center_iff.mp hc)
    ((imageRepresentation realizationData K).rangeRestrict R)
  have hh := congrArg Subtype.val hcomm
  change imageRepresentation realizationData K R*imageRepresentation realizationData K (sourceWeyl K)=
    imageRepresentation realizationData K (sourceWeyl K)*imageRepresentation realizationData K R at hh
  have he := DFunLike.congr_fun hh y
  change imageRepresentation realizationData K R
      (imageRepresentation realizationData K (sourceWeyl K) y)=
    imageRepresentation realizationData K (sourceWeyl K)
      (imageRepresentation realizationData K R y) at he
  rw [hRfix] at he
  have hv := congrArg Subtype.val he
  rw [long_root_image_action,hWy] at hv
  exact long_root_does_not_fix_weyl_root K hv

theorem imageProjective_even_card :
    Even (Nat.card (imageGroup K⧸Subgroup.center (imageGroup K))) := by
  let q := QuotientGroup.mk' (Subgroup.center (imageGroup K))
  apply CFSGProjectiveLinearEvenOrder.even_card_of_nontrivial_fourth_root (q (imageWeyl K))
  · intro h
    exact imageWeyl_not_center K ((QuotientGroup.eq_one_iff _).mp h)
  · exact (map_pow q (imageWeyl K) 4).symm.trans
      ((congrArg q (imageWeyl_four K)).trans (map_one q))

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
