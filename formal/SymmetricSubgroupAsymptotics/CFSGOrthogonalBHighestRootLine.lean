import SymmetricSubgroupAsymptotics.CFSGOrthogonalBHighestRootCoordinates
import Mathlib.Tactic.Abel

/-! The actual highest-root parameters form a faithful additive root
subgroup. A single nonzero parameter has the same full centralizer as
the entire original root line. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

def highestRootCoefficient (s : ℕ) : Mat K (s + 3) :=
  Matrix.single (pos (s + 3) 0) (neg (s + 3) (secondIndex s)) 1 -
    Matrix.single (pos (s + 3) (secondIndex s)) (neg (s + 3) 0) 1

theorem highestRootCoefficient_square (s : ℕ) :
    highestRootCoefficient (K := K) s * highestRootCoefficient s = 0 := by
  simp [highestRootCoefficient, sub_mul, mul_sub, pos, neg]

theorem highestRoot_add (h2 : (2 : K) ≠ 0) (s : ℕ) (a b : K) :
    highestRoot s (a + b) = highestRoot (K := K) s a * highestRoot s b := by
  apply Subtype.ext
  apply Units.ext
  change ((highestRoot s (a + b)).val : Mat K (s + 3)) =
    ((highestRoot s a).val : Mat K (s + 3)) * ((highestRoot s b).val : Mat K (s + 3))
  rw [highestRoot_val h2, highestRoot_val h2, highestRoot_val h2]
  change 1 + (a + b) • highestRootCoefficient s =
    (1 + a • highestRootCoefficient s) * (1 + b • highestRootCoefficient s)
  simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
    smul_smul, highestRootCoefficient_square, smul_zero, add_zero, add_smul]
  abel

def highestRootHom (h2 : (2 : K) ≠ 0) (s : ℕ) : Multiplicative K →*
    elementaryRootGroup K (s + 3) where
  toFun a := highestRoot s a.toAdd
  map_one' := highestRoot_zero h2 s
  map_mul' a b := highestRoot_add h2 s a.toAdd b.toAdd

def highestRootLine (h2 : (2 : K) ≠ 0) (s : ℕ) : Subgroup (elementaryRootGroup K (s + 3)) :=
  (highestRootHom h2 s).range

theorem mem_highestRootLine_iff (h2 : (2 : K) ≠ 0) (s : ℕ)
    (x : elementaryRootGroup K (s + 3)) :
    x ∈ highestRootLine h2 s ↔ ∃ a : K, x = highestRoot s a := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.toAdd, ha.symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.ofAdd a, rfl⟩

theorem commute_all_highestRoots_of_commute_nonzero (h2 : (2 : K) ≠ 0) (s : ℕ)
    (y : elementaryRootGroup K (s + 3)) (a : K) (ha : a ≠ 0)
    (h : Commute y (highestRoot s a)) (b : K) : Commute y (highestRoot s b) := by
  change y * highestRoot s a = highestRoot s a * y at h
  have he := congrArg (fun u : elementaryRootGroup K (s + 3) => (u.val : Mat K (s + 3))) h
  change (y.val : Mat K (s + 3)) * ((highestRoot s a).val : Mat K (s + 3)) =
    ((highestRoot s a).val : Mat K (s + 3)) * (y.val : Mat K (s + 3)) at he
  rw [highestRoot_val h2] at he
  change (y.val : Mat K (s + 3)) * (1 + a • highestRootCoefficient s) =
    (1 + a • highestRootCoefficient s) * (y.val : Mat K (s + 3)) at he
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc] at he
  have hY := (smul_right_injective (Mat K (s + 3)) ha) (add_left_cancel he)
  change y * highestRoot s b = highestRoot s b * y
  apply Subtype.ext
  apply Units.ext
  change (y.val : Mat K (s + 3)) * ((highestRoot s b).val : Mat K (s + 3)) =
    ((highestRoot s b).val : Mat K (s + 3)) * (y.val : Mat K (s + 3))
  rw [highestRoot_val h2]
  change (y.val : Mat K (s + 3)) * (1 + b • highestRootCoefficient s) =
    (1 + b • highestRootCoefficient s) * (y.val : Mat K (s + 3))
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hY]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
