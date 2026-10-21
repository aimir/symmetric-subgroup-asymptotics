import SymmetricSubgroupAsymptotics.CFSGSerreDividedPowerLocalFiniteness
import SymmetricSubgroupAsymptotics.CFSGSerreLocallyUnipotent
import SymmetricSubgroupAsymptotics.CFSGSerreRootDirection

/-! Every original four-term rootOperator is genuinely invertible. Its
positive-degree part is pointwise locally nilpotent by the actual divided-
power filtration. This does not assert exponential additivity or a uniform
adjoint nilpotence bound, neither of which follows from this argument. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
open CFSG.Models.Chevalley CFSGSerreDividedPowers
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]

def positiveRootPart (negative : Bool) (i : Fin n) (t : K) : Module.End K (Space A K) :=
  ∑ j ∈ Finset.range 3, t ^ (j + 1) • (integralOperator A negative i (j + 1)).baseChange K

theorem rootOperator_eq_one_add_positiveRootPart (negative : Bool) (i : Fin n) (t : K) :
    rootOperator A K negative i t = 1 + positiveRootPart A K negative i t := by
  simp [rootOperator, positiveRootPart, Finset.sum_range_succ, integralOperator_zero, add_assoc]

theorem positiveRootPart_lowers_tail (negative : Bool) (i : Fin n) (t : K)
    (N : ℕ) (x : Space A K)
    (hTail : ∀ k : ℕ, N + 1 ≤ k → (integralOperator A negative i k).baseChange K x = 0) :
    ∀ k : ℕ, N ≤ k → (integralOperator A negative i k).baseChange K
      (positiveRootPart A K negative i t x) = 0 := by
  intro k hk
  simp only [positiveRootPart, LinearMap.sum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  simp only [LinearMap.smul_apply, map_smul]
  have hz := hTail (k + (j + 1)) (by omega)
  have h := congrArg (fun f : Module.End K (Space A K) => f x)
    (baseChangedIntegralOperator_mul A K negative i k (j + 1))
  have hterm : (integralOperator A negative i k).baseChange K
      ((integralOperator A negative i (j + 1)).baseChange K x) = 0 := by
    simpa only [Module.End.mul_apply, LinearMap.smul_apply, hz, smul_zero] using h
  rw [hterm, smul_zero]

theorem positiveRootPart_pow_eq_zero_of_tail (negative : Bool) (i : Fin n) (t : K)
    (N : ℕ) (x : Space A K)
    (hTail : ∀ k : ℕ, N ≤ k → (integralOperator A negative i k).baseChange K x = 0) :
    (positiveRootPart A K negative i t ^ N) x = 0 := by
  induction N generalizing x with
  | zero =>
    have h := hTail 0 (Nat.zero_le _)
    simpa only [integralOperator_zero, LinearMap.baseChange_one, Module.End.one_apply,
      pow_zero] using h
  | succ N ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih (positiveRootPart A K negative i t x)
      (positiveRootPart_lowers_tail A K negative i t N x hTail)

theorem positiveRootPart_locally_nilpotent (negative : Bool) (i : Fin n) (t : K)
    (x : Space A K) : ∃ N : ℕ, (positiveRootPart A K negative i t ^ N) x = 0 := by
  obtain ⟨N, hN⟩ := baseChangedIntegralOperator_locally_finite A K negative i x
  exact ⟨N, positiveRootPart_pow_eq_zero_of_tail A K negative i t N x hN⟩

theorem rootOperator_bijective (negative : Bool) (i : Fin n) (t : K) :
    Function.Bijective (rootOperator A K negative i t) := by
  rw [rootOperator_eq_one_add_positiveRootPart]
  exact one_add_bijective_of_locally_nilpotent (positiveRootPart A K negative i t)
    (positiveRootPart_locally_nilpotent A K negative i t)

def rootEquiv (negative : Bool) (i : Fin n) (t : K) : Ambient A K :=
  LinearEquiv.ofBijective (rootOperator A K negative i t) (rootOperator_bijective A K negative i t)

@[simp] theorem rootEquiv_toLinearMap (negative : Bool) (i : Fin n) (t : K) :
    (rootEquiv A K negative i t).toLinearMap = rootOperator A K negative i t := rfl

theorem rootEquiv_isRootElement (negative : Bool) (i : Fin n) (t : K) :
    IsRootElement A K negative i t (rootEquiv A K negative i t) := rfl

/-- Every original displayed root parameter now has a genuine actual
linear automorphism witness. No separate invertibility certificate enters. -/
theorem rootElement_lifts (negative : Bool) (i : Fin n) (t : K) :
    ∃ g : Ambient A K, IsRootElement A K negative i t g :=
  ⟨rootEquiv A K negative i t, rfl⟩

theorem rootEquiv_mem_model (negative : Bool) (i : Fin n) (t : K) :
    rootEquiv A K negative i t ∈ subgroup A K :=
  Subgroup.subset_closure ⟨negative, i, t, rfl⟩

theorem rootEquiv_commute (negative : Bool) (i : Fin n) (a b : K) :
    Commute (rootEquiv A K negative i a) (rootEquiv A K negative i b) :=
  rootElements_commute A K negative i a b _ _ rfl rfl

end SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
