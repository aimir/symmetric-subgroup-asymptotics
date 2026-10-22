import SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortMembership
import Mathlib.Tactic.FieldSimp

/-! The actual negative short root kills the middle coordinate while
preserving every positive coordinate. Its quadratic negative-coordinate
term is retained throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationShortMembership
variable (K : Type) [Field K]

def negativeShortElement (s : ℕ) (i : Fin (s + 1)) (t : K) : elementaryRootGroup K (s + 1) :=
  ⟨shortUnit K (s + 1) (Sum.inr i) t, shortUnit_mem K s (Sum.inr i) t⟩

theorem negativeShort_positivePart (s : ℕ) (i : Fin (s + 1)) (t : K) (v : Index (s + 1) → K) :
    positivePart K (s + 1) (((negativeShortElement K s i t).val : Mat K (s + 1)) *ᵥ v) =
      positivePart K (s + 1) v := by
  change positivePart K (s + 1) ((shortUnit K (s + 1) (Sum.inr i) t : Mat K (s + 1)) *ᵥ v) = _
  rw [shortUnit_vector_action]
  funext j
  simp [positivePart, pos, middle, Pi.single_apply]

theorem negativeShort_middle (s : ℕ) (i : Fin (s + 1)) (t : K) (v : Index (s + 1) → K) :
    (((negativeShortElement K s i t).val : Mat K (s + 1)) *ᵥ v) (middle (s + 1)) =
      v (middle (s + 1)) - 2 * t * v (pos (s + 1) i) := by
  change ((shortUnit K (s + 1) (Sum.inr i) t : Mat K (s + 1)) *ᵥ v) (middle (s + 1)) = _
  rw [shortUnit_vector_action]
  simp [middle, pos, paired, Pi.single_apply]
  <;> ring

theorem negativeShort_kills_middle (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v : Index (s + 1) → K) (hv : positivePart K (s + 1) v = Pi.single 0 1) :
    let g := negativeShortElement K s 0 (v (middle (s + 1)) / 2)
    positivePart K (s + 1) ((g.val : Mat K (s + 1)) *ᵥ v) = Pi.single 0 1 ∧
      ((g.val : Mat K (s + 1)) *ᵥ v) (middle (s + 1)) = 0 := by
  dsimp only
  refine ⟨(negativeShort_positivePart K s _ _ v).trans hv, ?_⟩
  rw [negativeShort_middle]
  have hv0 := congrFun hv 0
  change v (pos (s + 1) 0) = 1 at hv0
  rw [hv0]
  field_simp [h2]
  <;> ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
