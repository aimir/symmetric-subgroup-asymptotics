import SymmetricSubgroupAsymptotics.SchurRepresentation
import SymmetricSubgroupAsymptotics.PrimeActionQuotient
import SymmetricSubgroupAsymptotics.PrimeFrattini

/-!
# Fractional Schur bound for actual survival-restricted lifts

The source is the actual Sylow subgroup of the original kernel, with the
action of its actual normalizer. Its elementary quotient is proved to be
the original Frattini quotient. Only the target action is inflated from B;
its capacity is the original simple-socle Schur capacity over F_p.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {J B Q : Type} [Group J] [Group B] [Group Q]

/-- Every finite prime-field module has its actual elementary p-group
as additive underlying group. -/
theorem primeModule_isPGroup (M : Rep (ZMod p) B) [Finite M] :
    IsPGroup p (Multiplicative M) := by
  apply IsPGroup.of_card (n := Module.finrank (ZMod p) M)
  simpa using Module.natCard_eq_pow_finrank (K := ZMod p) (V := M)

/-- The remaining equivariant Hom fibre satisfies the fractional Schur
bound without any semisimplicity or source-quotient-action assumption. -/
theorem sylowEquivariantKernelHom_card_le_schur [Finite J]
    (β : J →* B) (hβ : Function.Surjective β) (P : Sylow p β.ker)
    (M : Rep (ZMod p) B) [Finite M] :
    (Nat.card (SylowEquivariantKernelHom β P M) : ℝ) ≤
      (p : ℝ) ^ (representationSchurCapacity M.ρ *
        Module.finrank (ZMod p) (PrimeAbelianization p (P : Subgroup β.ker))) := by
  rw [Nat.card_congr (sylowEquivariantPrimeHomEquiv p β P M)]
  simpa only [Nat.card_zmod] using intertwiningMap_card_le_original_schur
    (β.comp (quotientSylowNormalizer β P).subtype)
    (quotientSylowNormalizer_surjective β hβ P)
    (primeAbelianizationRepresentation p (quotientSylowConjugation p β P)) M.ρ

/-- Every original survival predicate is retained. The translation and H1
factors are separate from the Schur exponent and are not dropped. -/
theorem homomorphicLift_survival_card_le_schur [Finite J] [Finite Q]
    (π : Q →* B) (β : J →* B) (hβ : Function.Surjective β)
    (M : Rep (ZMod p) B) [Finite M] (E : OriginalKernelModuleChart π M)
    (P : Sylow p β.ker) (S : HomomorphicLift π β → Prop) :
    (Nat.card {f : HomomorphicLift π β // S f} : ℝ) ≤
      Nat.card M * Nat.card (groupCohomology.H1 M) *
        (p : ℝ) ^ (representationSchurCapacity M.ρ *
          Module.finrank (ZMod p) (PrimeAbelianization p (P : Subgroup β.ker))) := by
  have h := homomorphicLift_survival_card_le_Sylow π β hβ M E
    (primeModule_isPGroup p M) P S
  calc
    (Nat.card {f : HomomorphicLift π β // S f} : ℝ) ≤
        Nat.card M * Nat.card (groupCohomology.H1 M) *
          (Nat.card (SylowEquivariantKernelHom β P M) : ℝ) := by exact_mod_cast h
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sylowEquivariantKernelHom_card_le_schur p β hβ P M) (by positivity)

/-- A proved numerical rank bound on the actual Frattini quotient may
be substituted, while keeping the same original target capacity. -/
theorem homomorphicLift_survival_card_le_schur_of_rank_bound [Finite J] [Finite Q]
    (π : Q →* B) (β : J →* B) (hβ : Function.Surjective β)
    (M : Rep (ZMod p) B) [Finite M] (E : OriginalKernelModuleChart π M)
    (P : Sylow p β.ker) (S : HomomorphicLift π β → Prop) (b : ℝ)
    (hrank : (Module.finrank (ZMod p)
      (PrimeAbelianization p (P : Subgroup β.ker)) : ℝ) ≤ b / p) :
    (Nat.card {f : HomomorphicLift π β // S f} : ℝ) ≤
      Nat.card M * Nat.card (groupCohomology.H1 M) *
        (p : ℝ) ^ (representationSchurCapacity M.ρ * (b / p)) := by
  apply (homomorphicLift_survival_card_le_schur p π β hβ M E P S).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (Fact.out : p.Prime).one_lt.le
  · have hcap : 0 ≤ representationSchurCapacity M.ρ := by
      unfold representationSchurCapacity
      letI := Representation.instModuleMonoidAlgebraAsModule M.ρ
      letI := Representation.instIsScalarTowerMonoidAlgebraAsModule M.ρ
      exact schurCapacity_nonneg
    exact mul_le_mul_of_nonneg_left hrank hcap

end SymmetricSubgroupAsymptotics
