import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentFieldActions

/-! A scalar times a field map on the actual first coordinate determines
the entire torus-normalizing automorphism of the native Suzuki
unipotent group.  No whole rank-one recognition is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentScaledFieldActions
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent CFSGSuzukiUnipotentFieldActions

theorem first_torus (m : ℕ) (c : (Field m)ˣ) (x : unipotentSubgroup m) :
    firstParameter m (torusAutHom m c x) =
      (c : Field m)⁻¹ * firstParameter m x := by
  obtain ⟨a,b,hx⟩ := x.property
  have he : x = coordinateElement m a b := Subtype.ext hx
  change firstParameter m (torusAction m c x) = _
  rw [he, torusAction_coordinateElement]
  rfl

theorem eq_scaled_fieldAut_of_first (m : ℕ) (hm : 1 ≤ m)
    (f : MulAut (unipotentSubgroup m))
    (hf : f ∈ Subgroup.normalizer
      ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))))
    (c : (Field m)ˣ) (sigma : Field m ≃+* Field m)
    (hfirst : ∀ x, firstParameter m (f x) =
      (c : Field m) * sigma (firstParameter m x)) :
    f = torusAutHom m c⁻¹ * fieldAut m sigma := by
  have hc : torusAutHom m c ∈ Subgroup.normalizer
      ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))) :=
    Subgroup.le_normalizer (show torusAutHom m c ∈ (torusAutHom m).range from ⟨c,rfl⟩)
  have hg := (Subgroup.normalizer
    ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m)))).mul_mem hc hf
  have hnormalized : torusAutHom m c * f = fieldAut m sigma := by
    apply eq_fieldAut_of_first m hm _ hg sigma
    intro x
    change firstParameter m (torusAutHom m c (f x)) = sigma (firstParameter m x)
    rw [first_torus, hfirst, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero c), one_mul]
  calc
    f = (torusAutHom m c)⁻¹ * fieldAut m sigma :=
      (eq_inv_mul_iff_mul_eq).mpr hnormalized
    _ = torusAutHom m c⁻¹ * fieldAut m sigma := by rw [map_inv]

theorem coordinate_action_of_scaled_first (m : ℕ) (hm : 1 ≤ m)
    (f : MulAut (unipotentSubgroup m))
    (hf : f ∈ Subgroup.normalizer
      ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))))
    (c : (Field m)ˣ) (sigma : Field m ≃+* Field m)
    (hfirst : ∀ x, firstParameter m (f x) =
      (c : Field m) * sigma (firstParameter m x)) (a b : Field m) :
    f (coordinateElement m a b) = coordinateElement m
      ((c : Field m) * sigma a) ((c : Field m) * theta m (c : Field m) * sigma b) := by
  rw [eq_scaled_fieldAut_of_first m hm f hf c sigma hfirst]
  change torusAction m c⁻¹ (fieldAut m sigma (coordinateElement m a b)) = _
  rw [fieldAut_coordinate, torusAction_coordinateElement]
  simp only [Units.val_inv_eq_inv_val, inv_inv, map_inv₀, mul_inv_rev]
  congr 1
  ring

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentScaledFieldActions
