import SymmetricSubgroupAsymptotics.CFSGTypeAGeneralLinearCardBound
import Mathlib.Data.Nat.Prime.Basic

/-! A prime larger than the field-unit group survives both the actual
GL determinant kernel and the actual full central SL quotient. No order
formula for SL or projective SL, or recognition theorem, is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProjectiveLinearPrimeDivisor

variable {F I : Type*} [Field F] [Finite F] [Fintype I] [DecidableEq I]

theorem dvd_projective_of_dvd_general (p : ℕ) (hp : p.Prime)
    (hlarge : Nat.card Fˣ < p)
    (hdiv : p ∣ Nat.card (Matrix.GeneralLinearGroup I F)) :
    p ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup I F) := by
  letI : Finite (Matrix.SpecialLinearGroup I F) :=
    Finite.of_injective (fun A : Matrix.SpecialLinearGroup I F => A.val)
      Subtype.val_injective
  let f : Matrix.GeneralLinearGroup I F →* Fˣ := Matrix.GeneralLinearGroup.det
  have hi : f.ker.index ≤ Nat.card Fˣ := by
    rw [Subgroup.index_ker]
    exact Nat.card_le_card_of_injective (fun z : f.range => (z : Fˣ)) Subtype.val_injective
  have hker : p ∣ Nat.card f.ker := by
    have hd : p ∣ Nat.card f.ker*f.ker.index := by
      rw [f.ker.card_mul_index]
      exact hdiv
    rcases hp.dvd_mul.mp hd with hh | hh
    · exact hh
    · have hp_le := Nat.le_of_dvd (Nat.pos_of_ne_zero f.ker.index_ne_zero_of_finite) hh
      exact False.elim ((not_le_of_gt (hi.trans_lt hlarge)) hp_le)
  have hkerCard : Nat.card f.ker=Nat.card (Matrix.SpecialLinearGroup I F) :=
    Nat.card_congr CFSGTypeAGeneralLinearCardBound.determinantKernelEquiv
  have hSL : p ∣ Nat.card (Matrix.SpecialLinearGroup I F) := by
    rw [←hkerCard]
    exact hker
  have hz : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup I F)) < p :=
    (CFSGTypeAGeneralLinearCardBound.specialLinear_center_card_le_units
      (F := F) (n := I)).trans_lt hlarge
  have hc := (Subgroup.center (Matrix.SpecialLinearGroup I F)).card_mul_index
  change Nat.card (Subgroup.center (Matrix.SpecialLinearGroup I F))*
    Nat.card (Matrix.ProjectiveSpecialLinearGroup I F)=
      Nat.card (Matrix.SpecialLinearGroup I F) at hc
  have hd : p ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup I F))*
      Nat.card (Matrix.ProjectiveSpecialLinearGroup I F) := by
    rw [hc]
    exact hSL
  rcases hp.dvd_mul.mp hd with hh | hh
  · exact False.elim ((not_le_of_gt hz) (Nat.le_of_dvd
      (Nat.card_pos (α := Subgroup.center (Matrix.SpecialLinearGroup I F))) hh))
  · exact hh

end SymmetricSubgroupAsymptotics.ProjectiveLinearPrimeDivisor
