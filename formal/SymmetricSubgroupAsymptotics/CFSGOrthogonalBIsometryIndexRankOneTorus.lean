import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortMembership
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationTerminalWeyl
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-! The rank-one square torus is an explicit six-short-root word in
the original B elementary group. Its literal three-coordinate diagonal
is proved directly, without identifying B1 with PSL2 or SO3. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneTorus
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationShortMembership CFSGOrthogonalBGenerationTerminalWeyl
variable (K : Type) [Field K]

def scaledWeyl (a : Kˣ) : elementaryRootGroup K 1 :=
  ⟨shortUnit K 1 (Sum.inl 0) (-(a : K)) *
      shortUnit K 1 (Sum.inr 0) (-((a : K)⁻¹)) * shortUnit K 1 (Sum.inl 0) (-(a : K)),
    (elementaryRootGroup K 1).mul_mem
      ((elementaryRootGroup K 1).mul_mem (shortUnit_mem K 0 (Sum.inl 0) _)
        (shortUnit_mem K 0 (Sum.inr 0) _)) (shortUnit_mem K 0 (Sum.inl 0) _)⟩

set_option maxHeartbeats 600000 in
theorem scaledWeyl_val (a : Kˣ) :
    ((scaledWeyl K a).val : Mat K 1) =
      Matrix.single (pos 1 0) (neg 1 0) (-((a : K) ^ 2)) +
      Matrix.single (neg 1 0) (pos 1 0) (-((a : K)⁻¹ ^ 2)) +
      Matrix.single (middle 1) (middle 1) (-1) := by
  change ((shortUnit K 1 (Sum.inl 0) (-(a : K)) : Mat K 1) *
    (shortUnit K 1 (Sum.inr 0) (-((a : K)⁻¹)) : Mat K 1)) *
    (shortUnit K 1 (Sum.inl 0) (-(a : K)) : Mat K 1) = _
  simp only [shortUnit_val]
  ext i j
  rcases i with ((i | i) | ⟨⟩) <;> rcases j with ((j | j) | ⟨⟩)
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [Matrix.mul_apply, Fintype.sum_sum_type, shortArray, shortSecond,
    paired, pos, neg, middle, Matrix.single_apply, Matrix.one_apply]
  all_goals field_simp [Units.ne_zero a]
  all_goals ring

def squareTorus (a : Kˣ) : elementaryRootGroup K 1 := scaledWeyl K a * terminalWeyl K 0

def squareDiagonal (a : Kˣ) : Index 1 → K
  | .inl (.inl _) => (a : K) ^ 2
  | .inl (.inr _) => (a : K)⁻¹ ^ 2
  | .inr _ => 1

theorem squareTorus_val (a : Kˣ) :
    ((squareTorus K a).val : Mat K 1) = Matrix.diagonal (squareDiagonal K a) := by
  change ((scaledWeyl K a).val : Mat K 1) * ((terminalWeyl K 0).val : Mat K 1) = _
  rw [scaledWeyl_val, terminalWeyl_val]
  ext i j
  rcases i with ((i | i) | ⟨⟩) <;> rcases j with ((j | j) | ⟨⟩)
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [Matrix.mul_apply, terminalArray, squareDiagonal,
    pos, neg, middle, Matrix.single_apply, Matrix.one_apply]
  all_goals ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneTorus
