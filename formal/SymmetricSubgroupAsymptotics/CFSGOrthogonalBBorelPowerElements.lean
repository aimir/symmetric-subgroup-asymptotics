import SymmetricSubgroupAsymptotics.CFSGOrthogonalBBorelPSubgroups

/-! A single actual defining-prime-power element of the same Borel
already lies in its unipotent subgroup. No order/cardinality surrogate
or subgroup replacement is needed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

private theorem upper_diagonal_pow {I : Type*} [Fintype I] [DecidableEq I]
    {m : ℕ} (e : I ≃ Fin m) {A : Matrix I I K}
    (hA : A.BlockTriangular e) (k : ℕ) (i : I) : (A ^ k) i i = (A i i) ^ k := by
  induction k with
  | zero => simp only [pow_zero, Matrix.one_apply_eq]
  | succ k ih =>
    rw [pow_succ, CFSGMatrixFlagSubgroups.upper_diag_mul e (hA.pow k) hA, ih, pow_succ]

theorem pPower_element_mem_unipotent (p n : ℕ) [Fact p.Prime] [CharP K p]
    (g : elementaryRootGroup K n) (hg : g ∈ borel K n) (k : ℕ) (hk : g ^ (p ^ k) = 1) :
    g ∈ unipotent K n := by
  have htri : (g.val : Mat K n).BlockTriangular (flagEquiv n) := hg
  refine ⟨htri, ?_⟩
  intro i
  have hp : (g.val : Mat K n) ^ (p ^ k) = 1 :=
    congrArg (fun x : elementaryRootGroup K n => (x.val : Mat K n)) hk
  have he := congrArg (fun A : Mat K n => A i i) hp
  dsimp only at he
  rw [upper_diagonal_pow (flagEquiv n) htri, Matrix.one_apply_eq] at he
  apply iterateFrobenius_inj K p k
  simpa only [iterateFrobenius_def, one_pow] using he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
