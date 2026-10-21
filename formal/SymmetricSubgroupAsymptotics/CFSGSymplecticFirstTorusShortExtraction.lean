import SymmetricSubgroupAsymptotics.CFSGSymplecticCleanLongPropagation

/-! The actual first-coordinate torus extracts a nonzero first short
root from the cleaned mixed word. The two commuting coordinate tori
and all scaling identities are proved on the original natural matrices. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem firstTorus_short_conjugation (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (g : Kˣ) (a : K) :
    firstTorus K r g * initialShortRoot K r a * (firstTorus K r g)⁻¹ =
      initialShortRoot K r ((g : K)⁻¹ * a) := by
  have h01 : (0 : Fin (r + 1)) ≠ (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  apply initialShort_diagonal_conjugation K r hr (firstTorus K r g)
    (coordinateTorusDiagonal K r 0 g) (firstTorus_coe K r g)
  · simp [coordinateTorusDiagonal, h01, Ne.symm h01]
  · simp [coordinateTorusDiagonal, h01, Ne.symm h01]

theorem secondTorus_short_conjugation (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (g : Kˣ) (a : K) :
    secondTorus K r g * initialShortRoot K r a * (secondTorus K r g)⁻¹ =
      initialShortRoot K r ((g : K) * a) := by
  have h01 : (0 : Fin (r + 1)) ≠ (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  apply initialShort_diagonal_conjugation K r hr (secondTorus K r g)
    (coordinateTorusDiagonal K r (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) g)
    (secondTorus_coe K r hr g)
  · simp [coordinateTorusDiagonal, h01, Ne.symm h01]
  · simp [coordinateTorusDiagonal, h01, Ne.symm h01]

theorem first_second_tori_commute (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) :
    Commute (secondTorus K r g) (firstTorus K r g) := by
  change secondTorus K r g * firstTorus K r g = firstTorus K r g * secondTorus K r g
  apply Subtype.ext
  apply Units.ext
  change ((secondTorus K r g).val : Mat K (r + 1)) *
      ((firstTorus K r g).val : Mat K (r + 1)) =
    ((firstTorus K r g).val : Mat K (r + 1)) *
      ((secondTorus K r g).val : Mat K (r + 1))
  rw [secondTorus_coe K r hr, firstTorus_coe,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem initial_short_extraction_mem (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (g : Kˣ) (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hT : firstTorus K r g ∈ H) (hY : cleanMixedWeyl K r ∈ H) :
    initialShortRoot K r ((1 - (g : K)) * (1 - (g : K)⁻¹)) ∈ H := by
  exact CFSGRootSubgroupExtraction.root_mem_of_twisted_torus
    (initialShortRoot K r) (initialShortRoot_add K r) (initialShortRoot_zero K r)
    (firstTorus K r g) (coxeterWeyl K r) (g : K)⁻¹ (g : K)
    (firstTorus_short_conjugation K r hr g)
    (secondTorus_short_conjugation K r hr g)
    (first_second_tori_commute K r hr g) H hT hY

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
