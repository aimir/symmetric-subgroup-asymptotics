import SymmetricSubgroupAsymptotics.CFSGTypeAGeneralLinearCardBound
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! The actual scalar quotient PGL has at most n times the order of PSL.
The factor n is the proved polynomial-root bound for the actual SL centre;
no formula for the outer automorphism group is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveLinearCardComparison
open Matrix CFSGTypeAGeneralLinearCardBound
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n] [Nonempty n]

theorem specialLinear_center_card_le_dimension :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup n F)) ≤ Fintype.card n := by
  letI : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
    (n := n) (R := F) (Classical.arbitrary n)).toEquiv, Nat.card_eq_fintype_card]
  exact card_rootsOfUnity F (Fintype.card n)

theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar n : Fˣ → Matrix.GeneralLinearGroup n F) := by
  intro a b hab
  obtain ⟨i⟩ := ‹Nonempty n›
  apply Units.ext
  have hentry := congrArg (fun A : Matrix.GeneralLinearGroup n F => A.val i i) hab
  simpa [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply] using hentry

theorem generalLinear_center_card_eq_units :
    Nat.card (Subgroup.center (Matrix.GeneralLinearGroup n F)) = Nat.card Fˣ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact (Nat.card_congr (MonoidHom.ofInjective (scalar_injective (F := F) (n := n))).toEquiv).symm

theorem projective_card_mul_units [Finite F] :
    Nat.card (Matrix.ProjGenLinGroup n F) * Nat.card Fˣ =
      Nat.card (Matrix.GeneralLinearGroup n F) := by
  have h := (Subgroup.center (Matrix.GeneralLinearGroup n F)).card_mul_index
  rw [generalLinear_center_card_eq_units] at h
  exact (Nat.mul_comm _ _).trans h

theorem projective_card_le_dimension_mul_specialProjective [Finite F] :
    Nat.card (Matrix.ProjGenLinGroup n F) ≤
      Fintype.card n * Nat.card (Matrix.ProjectiveSpecialLinearGroup n F) := by
  have hSL := (Subgroup.center (Matrix.SpecialLinearGroup n F)).card_mul_index
  change Nat.card (Subgroup.center (Matrix.SpecialLinearGroup n F)) *
    Nat.card (Matrix.ProjectiveSpecialLinearGroup n F) =
      Nat.card (Matrix.SpecialLinearGroup n F) at hSL
  have hGL := generalLinear_card_le_specialLinear_mul_units (F := F) (n := n)
  have hcentre := specialLinear_center_card_le_dimension (F := F) (n := n)
  have hpos : 0 < Nat.card Fˣ := Nat.card_pos
  apply Nat.le_of_mul_le_mul_right (c := Nat.card Fˣ)
  · rw [projective_card_mul_units]
    calc
      Nat.card (Matrix.GeneralLinearGroup n F) ≤
          Nat.card (Matrix.SpecialLinearGroup n F) * Nat.card Fˣ := hGL
      _ = (Nat.card (Subgroup.center (Matrix.SpecialLinearGroup n F)) *
          Nat.card (Matrix.ProjectiveSpecialLinearGroup n F)) * Nat.card Fˣ := by
        rw [← hSL]
      _ ≤ (Fintype.card n * Nat.card (Matrix.ProjectiveSpecialLinearGroup n F)) *
          Nat.card Fˣ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcentre)
  · exact hpos

end SymmetricSubgroupAsymptotics.CFSGProjectiveLinearCardComparison
