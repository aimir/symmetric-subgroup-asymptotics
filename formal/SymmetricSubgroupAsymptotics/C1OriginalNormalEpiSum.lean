import SymmetricSubgroupAsymptotics.RegularKernelHomBound
import SymmetricSubgroupAsymptotics.FusionEpimorphismLifts
import SymmetricSubgroupAsymptotics.OriginalKernelArbitraryNormalQuotient
import SymmetricSubgroupAsymptotics.C1OwnerAggregate

/-!
# Fixed-source original-normal sums for regular kernel sections

Every normal axis below is a literal normal subgroup of the original
group. Its quotient is the original `G/N`, with the exact kernel section
and acting top constructed by `OriginalKernelArbitraryNormalQuotient`.
The same complete source J is retained through the entire normal sum.

A regular embedding reduces each axis to an explicit character mass over
the actual top epimorphisms. The final physical theorem consumes a bound
on that mass, not a supplied quotient-epimorphism or physical-count bound.
In particular it does not prove the missing A4 or degree-nine top estimates.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

/-- The exact fixed-source top-map mass. Each summand uses the kernel of
that same onto map; neither its rank nor the number of top maps is assumed. -/
def regularTopCharacterMass (J B : Type) [Group J] [Group B]
    [Finite J] [Finite B] : ℕ :=
  ∑ β : GroupEpimorphism J B, Nat.card (PrimeCharacters p β.1.ker)

section Extension

variable {J Q B : Type} [Group J] [Group Q] [Group B]
variable [Finite J] [Finite Q] [Finite B]

/-- Sum the surviving fibres over their original top epimorphisms only
after applying the same-kernel regular-module injection. -/
theorem fusionEpimorphism_survival_card_le_regular
    (π : Q →* B) (hπ : Function.Surjective π)
    (M : Rep (ZMod p) B) [Finite M] (E : OriginalKernelModuleChart π M)
    (F : M.ρ.IntertwiningMap (Representation.leftRegular (ZMod p) B))
    (hF : Function.Injective F) (S : GroupEpimorphism J Q → Prop) :
    Nat.card {f : GroupEpimorphism J Q // S f} ≤
      (Nat.card M * Nat.card (groupCohomology.H1 M)) * regularTopCharacterMass p J B := by
  rw [fusionEpimorphism_survival_card π hπ S]
  calc
    _ ≤ ∑ β : GroupEpimorphism J B,
        (Nat.card M * Nat.card (groupCohomology.H1 M)) *
          Nat.card (PrimeCharacters p β.1.ker) := by
      apply Finset.sum_le_sum
      intro β _
      exact homomorphicLift_survival_card_le_regular p π β.1 β.2 M E F hF
        (FusionEpimorphismLiftSurvival π S β)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The top-map mass can be bounded separately by the actual number of
onto maps and a proved uniform character-rank bound on their kernels. -/
theorem regularTopCharacterMass_le_of_rank (r : ℕ)
    (hr : ∀ β : GroupEpimorphism J B,
      Module.finrank (ZMod p) (PrimeCharacters p β.1.ker) ≤ r) :
    regularTopCharacterMass p J B ≤ Nat.card (GroupEpimorphism J B) * p ^ r := by
  calc
    _ ≤ ∑ _β : GroupEpimorphism J B, p ^ r := by
      apply Finset.sum_le_sum
      intro β _
      rw [Module.natCard_eq_pow_finrank (K := ZMod p)
        (V := PrimeCharacters p β.1.ker), Nat.card_zmod]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (hr β)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card, Nat.cast_id]

end Extension

section OriginalNormal

variable {G B : Type} [Group G] [Group B] [Finite G]
variable (π : G →* B) (M : Rep (ZMod p) B) [Finite M]
variable (E : OriginalKernelModuleChart π M)

/-- The genuine finite extension constant of an original normal axis.
The cohomology factor is retained, even for a nonsplit original quotient. -/
def originalNormalRegularConstant (N : {N : Subgroup G // N.Normal}) : ℕ :=
  Nat.card (E.sectionRepresentation π M N.1) *
    Nat.card (groupCohomology.H1 (E.sectionRepresentation π M N.1))

/-- One arbitrary original normal axis, with its literal descended top. -/
theorem originalNormal_survival_card_le_regular
    {J : Type} [Group J] [Finite J]
    (N : {N : Subgroup G // N.Normal})
    (hregular : ∃ F : (E.sectionRepresentation π M N.1).ρ.IntertwiningMap
      (Representation.leftRegular (ZMod p) (G ⧸ (π.ker ⊔ N.1))),
      Function.Injective F)
    (S : GroupEpimorphism J (G ⧸ N.1) → Prop) :
    Nat.card {f : GroupEpimorphism J (G ⧸ N.1) // S f} ≤
      originalNormalRegularConstant p π M E N *
        regularTopCharacterMass p J (G ⧸ (π.ker ⊔ N.1)) := by
  obtain ⟨F, hF⟩ := hregular
  letI : Finite (E.sectionRepresentation π M N.1) :=
    Finite.of_surjective (E.normalSpace π M N.1).mkQ
      (E.normalSpace π M N.1).mkQ_surjective
  exact fusionEpimorphism_survival_card_le_regular p
    (OriginalKernelModuleChart.base π N.1)
    (OriginalKernelModuleChart.base_surjective π N.1)
    (E.sectionRepresentation π M N.1) (E.quotientChart π M N.1) F hF S

/-- Complete original-normal sum for one fixed source. Every surviving
quotient epimorphism is charged to its actual top map and actual kernel. -/
theorem originalNormal_survival_sum_le_regular
    {J : Type} [Group J] [Finite J]
    (hregular : ∀ N : {N : Subgroup G // N.Normal},
      ∃ F : (E.sectionRepresentation π M N.1).ρ.IntertwiningMap
        (Representation.leftRegular (ZMod p) (G ⧸ (π.ker ⊔ N.1))),
        Function.Injective F)
    (S : ∀ N : {N : Subgroup G // N.Normal}, GroupEpimorphism J (G ⧸ N.1) → Prop) :
    (∑ N : {N : Subgroup G // N.Normal},
      Nat.card {f : GroupEpimorphism J (G ⧸ N.1) // S N f}) ≤
      ∑ N : {N : Subgroup G // N.Normal},
        originalNormalRegularConstant p π M E N *
          regularTopCharacterMass p J (G ⧸ (π.ker ⊔ N.1)) := by
  exact Finset.sum_le_sum fun N _ =>
    originalNormal_survival_card_le_regular p π M E N (hregular N) (S N)

/-- Only the explicit top-map character masses remain as numerical
hypotheses. Constants are absorbed after the literal normal sum. -/
theorem originalNormal_survival_sum_le_of_mass
    {J : Type} [Group J] [Finite J]
    (hregular : ∀ N : {N : Subgroup G // N.Normal},
      ∃ F : (E.sectionRepresentation π M N.1).ρ.IntertwiningMap
        (Representation.leftRegular (ZMod p) (G ⧸ (π.ker ⊔ N.1))),
        Function.Injective F)
    (S : ∀ N : {N : Subgroup G // N.Normal}, GroupEpimorphism J (G ⧸ N.1) → Prop)
    (C : {N : Subgroup G // N.Normal} → ℝ) (X : ℝ)
    (hmass : ∀ N : {N : Subgroup G // N.Normal},
      (regularTopCharacterMass p J (G ⧸ (π.ker ⊔ N.1)) : ℝ) ≤ C N * X) :
    (∑ N : {N : Subgroup G // N.Normal},
      (Nat.card {f : GroupEpimorphism J (G ⧸ N.1) // S N f} : ℝ)) ≤
      (∑ N : {N : Subgroup G // N.Normal},
        (originalNormalRegularConstant p π M E N : ℝ) * C N) * X := by
  calc
    _ ≤ ∑ N : {N : Subgroup G // N.Normal},
        (originalNormalRegularConstant p π M E N : ℝ) *
          (regularTopCharacterMass p J (G ⧸ (π.ker ⊔ N.1)) : ℝ) := by
      apply Finset.sum_le_sum
      intro N _
      exact_mod_cast originalNormal_survival_card_le_regular p π M E N
        (hregular N) (S N)
    _ ≤ ∑ N : {N : Subgroup G // N.Normal},
        (originalNormalRegularConstant p π M E N : ℝ) * (C N * X) := by
      exact Finset.sum_le_sum fun N _ => mul_le_mul_of_nonneg_left (hmass N)
        (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_mul]; simp only [mul_assoc]

end OriginalNormal

/-- The original-weight C1 physical consumer. The structural inputs are
the actual arbitrary-normal quotient charts and regular embeddings. Its
remaining numerical input concerns only actual top-map character masses;
neither a final normal-sum nor a physical-count inequality is supplied. -/
theorem c1EarlierPhysical_regular_owner_bound
    (r : C1EarlierRow) (U : Subgroup (Equiv.Perm (Fin (c1EarlierWidth r))))
    {B : Type} [Group B] (π : U →* B) (M : Rep (ZMod p) B) [Finite M]
    (E : OriginalKernelModuleChart π M)
    (hregular : ∀ N : {N : Subgroup U // N.Normal},
      ∃ F : (E.sectionRepresentation π M N.1).ρ.IntertwiningMap
        (Representation.leftRegular (ZMod p) (U ⧸ (π.ker ⊔ N.1))),
        Function.Injective F)
    (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P) (C : {N : Subgroup U // N.Normal} → ℝ)
    (hmass : ∀ (J : Subgroup (Equiv.Perm (Fin b)))
      (N : {N : Subgroup U // N.Normal}),
      (regularTopCharacterMass p J (U ⧸ (π.ker ⊔ N.1)) : ℝ) ≤
        C N * ((b : ℝ) + 1) * (2 : ℝ) ^ (c1EarlierExponent r * b)) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + c1EarlierWidth r) ≤
      c1EarlierKernel b r
        (∑ N : {N : Subgroup U // N.Normal},
          (originalNormalRegularConstant p π M E N : ℝ) * C N)
        (Nat.card (Subgroup.normalizer
          (U : Set (Equiv.Perm (Fin (c1EarlierWidth r))))) : ℝ) *
        ((subgroupCount b : ℝ) / exactBenchmark b) := by
  apply c1EarlierPhysical_owner_bound r U b P hP
  intro J
  have h := originalNormal_survival_sum_le_of_mass p π M E hregular
    (fun N β => P (fusionFullGoursatEncode N J β).1) C
    (((b : ℝ) + 1) * (2 : ℝ) ^ (c1EarlierExponent r * b))
    (fun N => by simpa only [mul_assoc] using hmass J N)
  simpa only [fusionSurvivingEpiCount, mul_assoc] using h

/-- A source-restricted version for owners whose numerical top estimate
requires an actual orbit pattern. Outside that pattern the original
surviving epi fibres are proved empty, rather than given a fictitious
uniform top estimate. The source predicate is evaluated on the entire J. -/
theorem c1EarlierPhysical_regular_owner_bound_of_source
    (r : C1EarlierRow) (U : Subgroup (Equiv.Perm (Fin (c1EarlierWidth r))))
    {B : Type} [Group B] (π : U →* B) (M : Rep (ZMod p) B) [Finite M]
    (E : OriginalKernelModuleChart π M)
    (hregular : ∀ N : {N : Subgroup U // N.Normal},
      ∃ F : (E.sectionRepresentation π M N.1).ρ.IntertwiningMap
        (Representation.leftRegular (ZMod p) (U ⧸ (π.ker ⊔ N.1))),
        Function.Injective F)
    (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (Source : Subgroup (Equiv.Perm (Fin b)) → Prop)
    (hSource : ∀ (N : {N : Subgroup U // N.Normal})
      (J : Subgroup (Equiv.Perm (Fin b))) (β : GroupEpimorphism J (U ⧸ N.1)),
      P (fusionFullGoursatEncode N J β).1 → Source J)
    (C : {N : Subgroup U // N.Normal} → ℝ) (hC : ∀ N, 0 ≤ C N)
    (hmass : ∀ (J : Subgroup (Equiv.Perm (Fin b))), Source J →
      ∀ N : {N : Subgroup U // N.Normal},
      (regularTopCharacterMass p J (U ⧸ (π.ker ⊔ N.1)) : ℝ) ≤
        C N * ((b : ℝ) + 1) * (2 : ℝ) ^ (c1EarlierExponent r * b)) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + c1EarlierWidth r) ≤
      c1EarlierKernel b r
        (∑ N : {N : Subgroup U // N.Normal},
          (originalNormalRegularConstant p π M E N : ℝ) * C N)
        (Nat.card (Subgroup.normalizer
          (U : Set (Equiv.Perm (Fin (c1EarlierWidth r))))) : ℝ) *
        ((subgroupCount b : ℝ) / exactBenchmark b) := by
  apply c1EarlierPhysical_owner_bound r U b P hP
  intro J
  by_cases hJ : Source J
  · have h := originalNormal_survival_sum_le_of_mass p π M E hregular
      (fun N β => P (fusionFullGoursatEncode N J β).1) C
      (((b : ℝ) + 1) * (2 : ℝ) ^ (c1EarlierExponent r * b))
      (fun N => by simpa only [mul_assoc] using hmass J hJ N)
    simpa only [fusionSurvivingEpiCount, mul_assoc] using h
  · have hz (N : {N : Subgroup U // N.Normal}) :
        fusionSurvivingEpiCount U P N J = 0 := by
      letI : IsEmpty {β : GroupEpimorphism J (U ⧸ N.1) //
          P (fusionFullGoursatEncode N J β).1} :=
        ⟨fun f => hJ (hSource N J f.1 f.2)⟩
      simp only [fusionSurvivingEpiCount, Nat.card_of_isEmpty, Nat.cast_zero]
    rw [Finset.sum_eq_zero (fun N _ => hz N)]
    have hD : 0 ≤ ∑ N : {N : Subgroup U // N.Normal},
        (originalNormalRegularConstant p π M E N : ℝ) * C N :=
      Finset.sum_nonneg fun N _ => mul_nonneg (Nat.cast_nonneg _) (hC N)
    positivity

end SymmetricSubgroupAsymptotics

end
