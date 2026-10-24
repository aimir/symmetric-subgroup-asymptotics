import SymmetricSubgroupAsymptotics.SpecialLinearConjugacyFibre
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearGcdCardComparison
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! The exact original PSL order is obtained from the surjective determinant
and actual central scalar quotient. No order or recognition hypothesis is
added. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveSpecialLinearOrder
variable (F I : Type*) [Field F] [Finite F] [Fintype I] [DecidableEq I] [Nonempty I]

omit [Finite F] in
theorem generalLinear_card_eq_specialLinear_mul_units :
    Nat.card (Matrix.GeneralLinearGroup I F) =
      Nat.card (Matrix.SpecialLinearGroup I F) * (Nat.card F-1) := by
  let D : Matrix.GeneralLinearGroup I F →* Fˣ := Matrix.GeneralLinearGroup.det
  have h := D.ker.card_mul_index
  have hk : Nat.card D.ker = Nat.card (Matrix.SpecialLinearGroup I F) :=
    (Nat.card_congr (SpecialLinearConjugacyFibre.specialLinearKernelEquiv F I).toEquiv).symm
  have hi : D.ker.index = Nat.card Fˣ := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
      (SpecialLinearConjugacyFibre.determinant_surjective F I), Nat.card_congr (Subgroup.topEquiv.toEquiv)]
  rw [hk, hi, Nat.card_units] at h
  exact h.symm

theorem generalLinear_card_eq_projective_mul_units_gcd :
    Nat.card (Matrix.GeneralLinearGroup I F) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup I F) *
        ((Nat.card F-1) * (Nat.card F-1).gcd (Fintype.card I)) := by
  have h := (Subgroup.center (Matrix.SpecialLinearGroup I F)).card_mul_index
  change Nat.card (Subgroup.center (Matrix.SpecialLinearGroup I F)) *
    Nat.card (Matrix.ProjectiveSpecialLinearGroup I F) =
      Nat.card (Matrix.SpecialLinearGroup I F) at h
  rw [CFSGProjectiveLinearGcdCardComparison.specialLinear_center_card_eq_gcd] at h
  rw [generalLinear_card_eq_specialLinear_mul_units, ← h]
  ring

theorem projective_card_fin (n : ℕ) (hn : 0 < n) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) =
      (∏ i : Fin n, ((Nat.card F)^n - (Nat.card F)^(i : ℕ))) /
        ((Nat.card F-1) * (Nat.card F-1).gcd n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : Fintype F := Fintype.ofFinite F
  have h := generalLinear_card_eq_projective_mul_units_gcd F (Fin n)
  rw [Matrix.card_GL_field, Fintype.card_fin, ← Nat.card_eq_fintype_card] at h
  have hpos : 0 < (Nat.card F-1) * (Nat.card F-1).gcd n := by
    have hf : 2 ≤ Nat.card F := by simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F)
    exact Nat.mul_pos (by omega) (Nat.gcd_pos_of_pos_left n (by omega))
  rw [h, Nat.mul_div_cancel _ hpos]

end SymmetricSubgroupAsymptotics.CFSGProjectiveSpecialLinearOrder
