import SymmetricSubgroupAsymptotics.CFSGOrthogonalBVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortMembership
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTerminalVectorAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Original rank-one short-root words normalize every nonzero
singular vector up to a nonzero scalar. This is projective transitivity,
not the false assertion of transitivity on all singular vectors in B1. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneOrbit
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBGenerationShortArrays CFSGOrthogonalBGenerationShortMembership
open CFSGOrthogonalBGenerationTerminalWeyl CFSGOrthogonalBSingularVectorCount
variable (K : Type) [Field K]

theorem rank_one_norm (v : Index 1 → K) :
    (gram K 1).toBilin' v v = 4 * v (pos 1 0) * v (neg 1 0) + v (middle 1) ^ 2 := by
  rw [gram_norm_dot]
  simp [CFSGParabolicQuadricCount.dotDual, positivePart, negativePart]

theorem exists_scalar_normalize (h2 : (2 : K) ≠ 0) (v : Index 1 → K) (hv : v ≠ 0)
    (hs : (gram K 1).toBilin' v v = 0) :
    ∃ g : elementaryRootGroup K 1, ∃ a : K, a ≠ 0 ∧
      (g.val : Mat K 1) *ᵥ v = a • Pi.single (pos 1 0) 1 := by
  let x := v (pos 1 0)
  let y := v (neg 1 0)
  let z := v (middle 1)
  have hn : 4 * x * y + z ^ 2 = 0 := (rank_one_norm K v).symm.trans hs
  by_cases hx : x = 0
  · have hz : z = 0 := by
      have hh : z ^ 2 = 0 := by simpa only [hx, mul_zero, zero_mul, zero_add] using hn
      exact eq_zero_of_pow_eq_zero hh
    have hy : y ≠ 0 := by
      intro hy
      apply hv
      funext i
      rcases i with ((i | i) | ⟨⟩)
      · fin_cases i
        exact hx
      · fin_cases i
        exact hy
      · exact hz
    refine ⟨terminalWeyl K 0, -y, neg_ne_zero.mpr hy, ?_⟩
    rw [terminalWeyl_val]
    funext i
    rcases i with ((i | i) | ⟨⟩)
    all_goals try fin_cases i
    all_goals simp [terminalArray, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.single_mulVec,
      pos, neg, middle, x, y, z, hx, hz]
  · let t := z / (2 * x)
    let g : elementaryRootGroup K 1 :=
      ⟨shortUnit K 1 (Sum.inr 0) t, shortUnit_mem K 0 (Sum.inr 0) t⟩
    have h4 : (4 : K) ≠ 0 := by
      have he : (4 : K) = 2 * 2 := by ring
      rw [he]
      exact mul_ne_zero h2 h2
    have hy : y = -(z ^ 2) / (4 * x) := by
      apply (eq_div_iff (mul_ne_zero h4 hx)).mpr
      linear_combination hn
    have hmid : z + (-2) * t * x = 0 := by
      dsimp [t]
      field_simp [h2, hx] <;> ring
    have hneg : y + (t * z - t ^ 2 * x) = 0 := by
      rw [hy]
      dsimp [t]
      field_simp [h2, h4, hx] <;> ring
    refine ⟨g, x, hx, ?_⟩
    change (shortUnit K 1 (Sum.inr 0) t : Mat K 1) *ᵥ v = _
    rw [shortUnit_vector_action]
    funext i
    rcases i with (i | i) | i
    · fin_cases i
      simp [paired, pos, neg, middle, Pi.single_apply, x]
    · fin_cases i
      simpa [paired, pos, neg, middle, Pi.single_apply, x, y, z] using hneg
    · cases i
      simpa [paired, pos, neg, middle, Pi.single_apply, x, y, z] using hmid

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneOrbit
