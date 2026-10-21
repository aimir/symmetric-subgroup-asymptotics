import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations

/-! Each actual simple-root adjoint is locally nilpotent on the literal
Serre quotient, with a point-dependent exponent. This is not a uniform
fourth-power bound and does not justify the fixed truncated exponential. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
open CFSG.Models.Chevalley
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

theorem generator_adE_H (i j : Fin n) :
    (LieAlgebra.ad ℚ (RationalLie A) (generator A (.E i)) ^ 2) (generator A (.H j)) = 0 := by
  change ⁅generator A (.E i), ⁅generator A (.E i), generator A (.H j)⁆⁆ = 0
  rw [← lie_skew (generator A (.E i)) (generator A (.H j)), generator_HE]
  simp only [lie_neg, lie_zsmul, lie_self, smul_zero, neg_zero]

theorem generator_adF_H (i j : Fin n) :
    (LieAlgebra.ad ℚ (RationalLie A) (generator A (.F i)) ^ 2) (generator A (.H j)) = 0 := by
  change ⁅generator A (.F i), ⁅generator A (.F i), generator A (.H j)⁆⁆ = 0
  rw [← lie_skew (generator A (.F i)) (generator A (.H j)), generator_HF]
  simp only [lie_neg, lie_zsmul, lie_self, smul_zero, neg_zero]

theorem generator_adE_F (i j : Fin n) :
    (LieAlgebra.ad ℚ (RationalLie A) (generator A (.E i)) ^ 3) (generator A (.F j)) = 0 := by
  change ⁅generator A (.E i), ⁅generator A (.E i), ⁅generator A (.E i), generator A (.F j)⁆⁆⁆ = 0
  by_cases hij : i = j
  · subst j
    rw [generator_EF_same]
    exact generator_adE_H A i i
  · rw [generator_EF_ne A i j hij]
    simp

theorem generator_adF_E (i j : Fin n) :
    (LieAlgebra.ad ℚ (RationalLie A) (generator A (.F i)) ^ 3) (generator A (.E j)) = 0 := by
  change ⁅generator A (.F i), ⁅generator A (.F i), ⁅generator A (.F i), generator A (.E j)⁆⁆⁆ = 0
  by_cases hij : j = i
  · subst j
    rw [← lie_skew (generator A (.F i)) (generator A (.E i)), generator_EF_same]
    have h : ⁅generator A (.F i), ⁅generator A (.F i), generator A (.H i)⁆⁆ = 0 :=
      generator_adF_H A i i
    simpa only [lie_neg, neg_zero] using congrArg (fun x : RationalLie A => -x) h
  · rw [← lie_skew (generator A (.F i)) (generator A (.E j)), generator_EF_ne A j i hij]
    simp

theorem root_ad_nilpotent_on_generator (negative : Bool) (i : Fin n)
    (g : CartanMatrix.Generators (Fin n)) :
    ∃ k : ℕ, (LieAlgebra.ad ℚ (RationalLie A) (rootVector A negative i) ^ k) (generator A g) = 0 := by
  cases negative with
  | false =>
    change ∃ k : ℕ, (LieAlgebra.ad ℚ (RationalLie A) (generator A (.E i)) ^ k) (generator A g) = 0
    cases g with
    | H j => exact ⟨2, generator_adE_H A i j⟩
    | E j => exact ⟨(-A i j).toNat + 1, generator_adE A i j⟩
    | F j => exact ⟨3, generator_adE_F A i j⟩
  | true =>
    change ∃ k : ℕ, (LieAlgebra.ad ℚ (RationalLie A) (generator A (.F i)) ^ k) (generator A g) = 0
    cases g with
    | H j => exact ⟨2, generator_adF_H A i j⟩
    | E j => exact ⟨3, generator_adF_E A i j⟩
    | F j => exact ⟨(-A i j).toNat + 1, generator_adF A i j⟩

/-- The exponent genuinely depends on x; no finite-dimensionality or
finite-type matrix hypothesis is used. -/
theorem simpleRoot_ad_locally_nilpotent (negative : Bool) (i : Fin n) (x : RationalLie A) :
    ∃ k : ℕ, (LieAlgebra.ad ℚ (RationalLie A) (rootVector A negative i) ^ k) x = 0 := by
  have hgen : ∀ y ∈ Set.range (generator A),
      ∃ k : ℕ, ((adDerivation (R := ℚ) (rootVector A negative i)).toLinearMap ^ k) y = 0 := by
    rintro y ⟨g, rfl⟩
    simpa only [adDerivation_toLinearMap] using root_ad_nilpotent_on_generator A negative i g
  have h := locallyNilpotent_of_lieSpan_generators
    (adDerivation (R := ℚ) (rootVector A negative i)) (Set.range (generator A))
    (generator_lieSpan_eq_top A) hgen x
  simpa only [adDerivation_toLinearMap] using h

theorem integralOperator_one_coe_apply (negative : Bool) (i : Fin n) (x : integralLattice A) :
    (integralOperator A negative i 1 x).val =
      LieAlgebra.ad ℚ (RationalLie A) (rootVector A negative i) x.val := by
  change dividedPower A negative i 1 x.val = _
  simp [dividedPower]

theorem integralOperator_one_pow_coe (negative : Bool) (i : Fin n) (k : ℕ)
    (x : integralLattice A) :
    ((integralOperator A negative i 1 ^ k) x).val =
      (LieAlgebra.ad ℚ (RationalLie A) (rootVector A negative i) ^ k) x.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', Module.End.mul_apply, integralOperator_one_coe_apply, ih]

theorem integralOperator_one_locally_nilpotent (negative : Bool) (i : Fin n)
    (x : integralLattice A) : ∃ k : ℕ, (integralOperator A negative i 1 ^ k) x = 0 := by
  obtain ⟨k, hk⟩ := simpleRoot_ad_locally_nilpotent A negative i x.val
  refine ⟨k, ?_⟩
  apply Subtype.ext
  change ((integralOperator A negative i 1 ^ k) x).val = 0
  rw [integralOperator_one_pow_coe, hk]

end SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
