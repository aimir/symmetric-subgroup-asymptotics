import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
import Mathlib.Algebra.CharP.Reduced
import Mathlib.GroupTheory.PGroup

/-! An actual defining-characteristic p-subgroup of the B-Borel has
diagonal one. This retains the original subgroup and its original
matrix representation throughout the Frobenius argument. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices

private theorem flag_upper_diag_pow {I : Type*} [Fintype I] [DecidableEq I]
    {K : Type*} [Field K] {m : ℕ} (e : I ≃ Fin m)
    {A : Matrix I I K} (hA : A.BlockTriangular e) (k : ℕ) (i : I) :
    (A ^ k) i i = (A i i) ^ k := by
  induction k with
  | zero => simp only [pow_zero, Matrix.one_apply_eq]
  | succ k ih =>
    rw [pow_succ, CFSGMatrixFlagSubgroups.upper_diag_mul e (hA.pow k) hA, ih, pow_succ]

theorem pSubgroup_le_unipotent {K : Type} [Field K] {p n : ℕ}
    [Fact p.Prime] [CharP K p]
    (P : Subgroup (elementaryRootGroup K n)) (hP : IsPGroup p P)
    (hPB : P ≤ borel K n) : P ≤ unipotent K n := by
  intro g hg
  have htri : (g.val : Mat K n).BlockTriangular (flagEquiv n) := hPB hg
  refine ⟨htri, ?_⟩
  intro i
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hp : (g.val : Mat K n) ^ (p ^ k) = 1 :=
    congrArg (fun x : P => (x.val.val : Mat K n)) hk
  have he := congrArg (fun A : Mat K n => A i i) hp
  dsimp only at he
  rw [flag_upper_diag_pow (flagEquiv n) htri, Matrix.one_apply_eq] at he
  apply iterateFrobenius_inj K p k
  simpa only [iterateFrobenius_def, one_pow] using he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
