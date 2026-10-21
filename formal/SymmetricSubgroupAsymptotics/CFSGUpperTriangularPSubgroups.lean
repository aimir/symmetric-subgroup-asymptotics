import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
import Mathlib.Algebra.CharP.Reduced
import Mathlib.GroupTheory.PGroup

/-! Actual defining-characteristic p-subgroups of an upper-triangular
matrix group are unitriangular. Every diagonal cyclic factor is retained
until Frobenius injectivity proves that it is trivial. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
open Matrix

theorem upper_diag_pow {F : Type*} [Field F] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) F} (hA : A.BlockTriangular id)
    (k : ℕ) (i : Fin n) : (A^k) i i=(A i i)^k := by
  induction k with
  | zero => simp only [pow_zero,Matrix.one_apply_eq]
  | succ k ih => rw [pow_succ,upper_diag_mul (hA.pow k) hA,ih,pow_succ]

theorem pSubgroup_le_upperUnitriangular {F : Type*} [Field F]
    {p n : ℕ} [Fact p.Prime] [CharP F p]
    (P : Subgroup (SL F n)) (hP : IsPGroup p P) (hPB : P≤borel F n) :
    P≤upperUnitriangular F n := by
  intro g hg
  have htri : g.val.BlockTriangular id := hPB hg
  refine ⟨htri,?_⟩
  intro i
  obtain ⟨k,hk⟩ := hP ⟨g,hg⟩
  have hp : g.val^(p^k)=1 := congrArg (fun x : P => x.val.val) hk
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) F => A i i) hp
  dsimp only at he
  rw [upper_diag_pow htri,Matrix.one_apply_eq] at he
  apply iterateFrobenius_inj F p k
  simpa only [iterateFrobenius_def,one_pow] using he

end SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
