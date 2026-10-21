import SymmetricSubgroupAsymptotics.CFSGGTwoImageRealization
import SymmetricSubgroupAsymptotics.CFSGGTwoLongRootAction
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEvenOrder

/-! A fourth-root word is noncentral in the actual image action group.
The witness is tested on the SAME original E₁ generator image, so no
scalar-centralizer claim for the reducible natural representation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
open CFSG.Models.Chevalley

 abbrev naturalActionImage (K : Type) [Field K] := (naturalImageAction K).range
 def imageLongWeyl (K : Type) [Field K] : naturalActionImage K :=
  (naturalImageAction K).rangeRestrict (naturalLongWeyl K)

 theorem imageLongWeyl_four (K : Type) [Field K] : imageLongWeyl K^4=1 := by
  change ((naturalImageAction K).rangeRestrict (naturalLongWeyl K))^4=1
  rw [←map_pow,naturalLongWeyl_four,map_one]

 private theorem action_val (K : Type) [Field K] (g : naturalGroup K)
    (y : (foldedBaseChange K).range) :
    (naturalImageAction K g y).val=(g.val:Mat K)*y.val*(↑(g.val⁻¹):Mat K) := rfl

 theorem imageLongWeyl_not_center (K : Type) [Field K] :
    imageLongWeyl K∉Subgroup.center (naturalActionImage K) := by
  intro hc
  let u := naturalRoot K false 1 1
  let y : (foldedBaseChange K).range := (foldedBaseChange K).rangeRestrict
    (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator CartanMatrix.G₂ (CartanMatrix.Generators.E 1))
  have hy : y.val=positive K 1 := foldedBaseChange_E K 1
  have hufix : naturalImageAction K u y=y := by
    apply Subtype.ext
    rw [action_val,hy]
    change (rootTransvection K false 1 1:Mat K)*positive K 1*
      (↑((rootTransvection K false 1 1)⁻¹):Mat K)=positive K 1
    simpa only [rootTransvection_val,rootTransvection_inv_val,rootMatrix,rootSecond,
      Bool.false_eq_true,if_false,positiveSecond,if_neg (show (1:Fin 2)≠0 by decide),
      smul_zero,add_zero,one_smul] using positive_root_fixes_positive K
  have hw : (naturalImageAction K (naturalLongWeyl K) y).val= -negative K 1 := by
    rw [action_val,hy,naturalLongWeyl_val]
    exact longWeyl_conjugate_positive K
  have hcomm := (Subgroup.mem_center_iff.mp hc) ((naturalImageAction K).rangeRestrict u)
  have hh := congrArg Subtype.val hcomm
  change naturalImageAction K u*naturalImageAction K (naturalLongWeyl K)=
    naturalImageAction K (naturalLongWeyl K)*naturalImageAction K u at hh
  have he := DFunLike.congr_fun hh y
  change naturalImageAction K u (naturalImageAction K (naturalLongWeyl K) y)=
    naturalImageAction K (naturalLongWeyl K) (naturalImageAction K u y) at he
  rw [hufix] at he
  have hv := congrArg Subtype.val he
  rw [action_val,hw] at hv
  change (rootTransvection K false 1 1:Mat K)*(-negative K 1)*
    (↑((rootTransvection K false 1 1)⁻¹):Mat K)= -negative K 1 at hv
  simp only [rootTransvection_val,rootTransvection_inv_val,rootMatrix,rootSecond,
    Bool.false_eq_true,if_false,positiveSecond,if_neg (show (1:Fin 2)≠0 by decide),
    smul_zero,add_zero,one_smul] at hv
  have hhentry := congrArg (fun M : Mat K=>M (pos 1) (pos 2)) hv
  dsimp only at hhentry
  rw [positive_root_negative_entry,negative_entry] at hhentry
  exact one_ne_zero hhentry

 theorem imageProjective_even_card (K : Type) [Field K] :
    Even (Nat.card (naturalActionImage K⧸Subgroup.center (naturalActionImage K))) := by
  let q := QuotientGroup.mk' (Subgroup.center (naturalActionImage K))
  apply CFSGProjectiveLinearEvenOrder.even_card_of_nontrivial_fourth_root (q (imageLongWeyl K))
  · intro h
    exact imageLongWeyl_not_center K ((QuotientGroup.eq_one_iff _).mp h)
  · rw [←map_pow,imageLongWeyl_four,map_one]

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
