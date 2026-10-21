import SymmetricSubgroupAsymptotics.CFSGSerreSimpleRootLocalNilpotence
import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowers

/-! The actual divided-power sequence is eventually zero at each lattice
vector and at each vector after tensor base change. The cutoff is allowed
to depend on the vector, including after reduction in small characteristic. -/
set_option autoImplicit false
noncomputable section
open scoped Classical TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
open CFSG.Models.Chevalley
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

theorem integralOperator_locally_finite (negative : Bool) (i : Fin n) (x : integralLattice A) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → integralOperator A negative i k x = 0 := by
  obtain ⟨N, hN⟩ := simpleRoot_ad_locally_nilpotent A negative i x.val
  refine ⟨N, ?_⟩
  intro k hk
  apply Subtype.ext
  change ((k.factorial : ℚ)⁻¹) •
    (LieAlgebra.ad ℚ (RationalLie A) (rootVector A negative i) ^ k) x.val = 0
  rw [end_pow_apply_zero_of_le _ hN hk, smul_zero]

theorem baseChangedIntegralOperator_locally_finite (K : Type) [Field K]
    (negative : Bool) (i : Fin n) (x : Space A K) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → (integralOperator A negative i k).baseChange K x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun _ _ => map_zero _⟩
  | tmul a x =>
    obtain ⟨N, hN⟩ := integralOperator_locally_finite A negative i x
    refine ⟨N, ?_⟩
    intro k hk
    simp only [LinearMap.baseChange_tmul, hN k hk, TensorProduct.tmul_zero]
  | add x y hx hy =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hy
    refine ⟨N + M, ?_⟩
    intro k hk
    rw [map_add, hN k ((Nat.le_add_right N M).trans hk),
      hM k ((Nat.le_add_left M N).trans hk), add_zero]

end SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
