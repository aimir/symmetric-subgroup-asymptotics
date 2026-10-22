import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationElements
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBImageRealization
import Mathlib.Tactic.LinearCombination

/-! Noncommutativity on the SAME original B Serre-image space, in every
characteristic. The witness uses a chain root and tests its actual action
on its original E-generator image. No natural scalar-centralizer theorem
is required in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationImageNoncentral
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationElements
open CFSG.Models.Chevalley
variable (K : Type) [Field K]

private theorem chain_fixes_positive (r : ℕ) (i : Fin r) (hi : i.val + 1 < r) :
    (rootTransvection K r false i 1 : Mat K r) * positive K r i *
      (↑((rootTransvection K r false i 1)⁻¹) : Mat K r) = positive K r i := by
  have hn : (⟨i.val + 1, hi⟩ : Fin r) ≠ i := by
    intro he
    have hh := congrArg Fin.val he
    change i.val + 1 = i.val at hh
    omega
  simp only [rootTransvection_inv_val]
  simp [rootTransvection_val, rootMatrix, rootSecond,
    positive, positiveSecond, hi, mul_add, add_mul, mul_sub, sub_mul, hn, hn.symm]

private theorem negative_image_entry (r : ℕ) (i : Fin r) (hi : i.val + 1 < r) :
    ((rootTransvection K r true i 1 : Mat K r) * positive K r i *
      (↑((rootTransvection K r true i 1)⁻¹) : Mat K r)) (pos r i) (pos r i) = -1 := by
  have hn : (⟨i.val + 1, hi⟩ : Fin r) ≠ i := by
    intro he
    have hh := congrArg Fin.val he
    change i.val + 1 = i.val at hh
    omega
  simp only [rootTransvection_inv_val]
  simp [rootTransvection_val, rootMatrix, rootSecond,
    positive, negative, positiveSecond, negativeSecond, hi, mul_add, add_mul,
    mul_sub, sub_mul, pos, neg, middle, hn, hn.symm, Matrix.single_apply]

private theorem double_image_entry (r : ℕ) (i : Fin r) (hi : i.val + 1 < r) :
    ((rootTransvection K r false i 1 : Mat K r) *
      ((rootTransvection K r true i 1 : Mat K r) * positive K r i *
        (↑((rootTransvection K r true i 1)⁻¹) : Mat K r)) *
      (↑((rootTransvection K r false i 1)⁻¹) : Mat K r)) (pos r i) (pos r i) = -2 := by
  have hn : (⟨i.val + 1, hi⟩ : Fin r) ≠ i := by
    intro he
    have hh := congrArg Fin.val he
    change i.val + 1 = i.val at hh
    omega
  simp only [rootTransvection_inv_val]
  simp [rootTransvection_val, rootMatrix, rootSecond,
    positive, negative, positiveSecond, negativeSecond, hi, mul_add, add_mul,
    mul_sub, sub_mul, pos, neg, middle, hn, hn.symm, Matrix.single_apply]
  all_goals ring

abbrev ActionImage (r : ℕ) := (elementaryImageAction K r).range

theorem positive_image_not_center (r : ℕ) (i : Fin r) (hi : i.val + 1 < r) :
    (elementaryImageAction K r).rangeRestrict (rootElement K r false i 1) ∉
      Subgroup.center (ActionImage K r) := by
  intro hc
  let u := rootElement K r false i 1
  let v := rootElement K r true i 1
  let y : (orthogonalBaseChange K r).range := (orthogonalBaseChange K r).rangeRestrict
    (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.B r).transpose
      (CartanMatrix.Generators.E i))
  have hy : y.val = positive K r i := orthogonalBaseChange_E K r i
  have hu : elementaryImageAction K r u y = y := by
    apply Subtype.ext
    change (u.val : Mat K r) * y.val * (↑u.val⁻¹ : Mat K r) = y.val
    rw [hy]
    exact chain_fixes_positive K r i hi
  have hh := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hc)
    ((elementaryImageAction K r).rangeRestrict v))
  change elementaryImageAction K r v * elementaryImageAction K r u =
    elementaryImageAction K r u * elementaryImageAction K r v at hh
  have he := DFunLike.congr_fun hh y
  change elementaryImageAction K r v (elementaryImageAction K r u y) =
    elementaryImageAction K r u (elementaryImageAction K r v y) at he
  rw [hu] at he
  have hm := congrArg Subtype.val he
  change (v.val : Mat K r) * y.val * (↑v.val⁻¹ : Mat K r) =
    (u.val : Mat K r) * ((v.val : Mat K r) * y.val * (↑v.val⁻¹ : Mat K r)) *
      (↑u.val⁻¹ : Mat K r) at hm
  rw [hy] at hm
  have hd := congrArg (fun A : Mat K r => A (pos r i) (pos r i)) hm
  change ((rootTransvection K r true i 1 : Mat K r) * positive K r i *
      (↑((rootTransvection K r true i 1)⁻¹) : Mat K r)) (pos r i) (pos r i) =
    ((rootTransvection K r false i 1 : Mat K r) *
      ((rootTransvection K r true i 1 : Mat K r) * positive K r i *
        (↑((rootTransvection K r true i 1)⁻¹) : Mat K r)) *
      (↑((rootTransvection K r false i 1)⁻¹) : Mat K r)) (pos r i) (pos r i) at hd
  rw [negative_image_entry K r i hi, double_image_entry K r i hi] at hd
  have hbad : (1 : K) = 0 := by linear_combination hd
  exact one_ne_zero hbad

theorem imageProjective_nontrivial (r : ℕ) (hr : 2 ≤ r) :
    Nontrivial (ActionImage K r ⧸ Subgroup.center (ActionImage K r)) := by
  let i : Fin r := ⟨0, by omega⟩
  let a := (elementaryImageAction K r).rangeRestrict (rootElement K r false i 1)
  let q := QuotientGroup.mk' (Subgroup.center (ActionImage K r))
  apply nontrivial_of_ne (q a) 1
  intro he
  exact positive_image_not_center K r i (by change 0 + 1 < r; omega)
    ((QuotientGroup.eq_one_iff _).mp he)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationImageNoncentral
