import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryCenter
import Mathlib.Data.Finite.Card

/-! A deliberately coarse centre bound sufficient for the D index
cell: scalar recognition makes one literal diagonal entry injective.
No orthogonal-group order or preservation-of-form result is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexCenterCard
open CFSGOrthogonalDSerreMatrices
variable (K : Type*) [Field K]

def centerEntry (s : ℕ) (u : Subgroup.center (elementaryRootGroup K (s + 4))) : K :=
  (u.val.val : Mat K (s + 4)) (Sum.inl 0) (Sum.inl 0)

theorem centerEntry_injective (s : ℕ) : Function.Injective (centerEntry K s) := by
  intro u v h
  obtain ⟨a, ha⟩ := (elementaryRootGroup_center_iff_scalar K (s + 2) u.val).mp u.property
  obtain ⟨b, hb⟩ := (elementaryRootGroup_center_iff_scalar K (s + 2) v.val).mp v.property
  have hab : a = b := by
    change (u.val.val : Mat K (s + 4)) (Sum.inl 0) (Sum.inl 0) =
      (v.val.val : Mat K (s + 4)) (Sum.inl 0) (Sum.inl 0) at h
    simpa only [ha, hb, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using h
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [ha, hb, hab]

theorem center_card_le_field [Finite K] (s : ℕ) :
    Nat.card (Subgroup.center (elementaryRootGroup K (s + 4))) ≤ Nat.card K :=
  Nat.card_le_card_of_injective (centerEntry K s) (centerEntry_injective K s)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexCenterCard
