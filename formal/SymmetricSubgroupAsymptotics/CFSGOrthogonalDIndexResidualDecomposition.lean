import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailDecomposition
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualCorrection
import Mathlib.Tactic.Abel

/-! Every vector perpendicular to the original first positive axis has
an explicit head/companion/corrected-tail decomposition. In particular,
the residual summand used below is the SAME literal quadratic space,
not an unproved choice of a Witt complement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualDecomposition
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexResidualCorrection CFSGOrthogonalDIndexBundledQuadratic
open CFSGHyperbolicTransverseCorrection
variable (K : Type) [Field K]

theorem residualMap_apply (n : ℕ) (w : Index (n + 2) → K) (z : Index n → K) :
    residualMap K n w z = twiceTailExtension K n z -
      (((splitQuadraticForm K (n + 2)).polarBilin w
        (Pi.single (Sum.inl (tailSecondIndex n)) 1))⁻¹ *
        (splitQuadraticForm K (n + 2)).polarBilin w (twiceTailExtension K n z)) •
          Pi.single (Sum.inl (tailSecondIndex n)) 1 := rfl

theorem companion_pairing_eq_coordinate (n : ℕ) (w : Index (n + 2) → K) :
    (splitQuadraticForm K (n + 2)).polarBilin w
        (Pi.single (Sum.inl (tailSecondIndex n)) 1) =
      w (Sum.inr (tailSecondIndex n)) := by
  change QuadraticMap.polar (splitQuadraticForm K (n + 2)) w
    (Pi.single (Sum.inl (tailSecondIndex n)) 1) = w (Sum.inr (tailSecondIndex n))
  rw [QuadraticMap.polar_comm (splitQuadraticForm K (n + 2) : (Index (n + 2) → K) → K)]
  exact positive_polar K (n + 2) (tailSecondIndex n) w

theorem exists_residual_decomposition (n : ℕ) (w t : Index (n + 2) → K)
    (hw0 : w (Sum.inr 0) = 0)
    (hc : (splitQuadraticForm K (n + 2)).polarBilin w
      (Pi.single (Sum.inl (tailSecondIndex n)) 1) ≠ 0)
    (ht0 : t (Sum.inr 0) = 0) :
    ∃ (a b c : K) (z : Index n → K),
      t = a • Pi.single (Sum.inl (0 : Fin (n + 2))) 1 +
        b • Pi.single (Sum.inl (tailSecondIndex n)) 1 + c • w + residualMap K n w z := by
  have hw1 : w (Sum.inr (tailSecondIndex n)) ≠ 0 := by
    rwa [companion_pairing_eq_coordinate] at hc
  let c : K := t (Sum.inr (tailSecondIndex n)) / w (Sum.inr (tailSecondIndex n))
  let v := t - c • w
  have hv0 : v (Sum.inr 0) = 0 := by
    simp [v, ht0, hw0]
  have hv1 : v (Sum.inr (tailSecondIndex n)) = 0 := by
    simp [v, c, div_mul_cancel₀ _ hw1]
  let z := twiceTailRestriction K n v
  let d := ((splitQuadraticForm K (n + 2)).polarBilin w
      (Pi.single (Sum.inl (tailSecondIndex n)) 1))⁻¹ *
        (splitQuadraticForm K (n + 2)).polarBilin w (twiceTailExtension K n z)
  have he := twice_head_tail_decomposition K n v hv0 hv1
  have ht : t = v + c • w := (sub_add_cancel t (c • w)).symm
  refine ⟨v (Sum.inl 0), v (Sum.inl (tailSecondIndex n)) + d, c, z, ?_⟩
  calc
    t = (v (Sum.inl 0) • Pi.single (Sum.inl (0 : Fin (n + 2))) 1 +
        v (Sum.inl (tailSecondIndex n)) • Pi.single (Sum.inl (tailSecondIndex n)) 1 +
        twiceTailExtension K n z) + c • w :=
      ht.trans (congrArg (fun q => q + c • w) he)
    _ = _ := by
      rw [residualMap_apply, add_smul]
      change _ = _ + _ + _ + (twiceTailExtension K n z - d • _)
      abel

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualDecomposition
