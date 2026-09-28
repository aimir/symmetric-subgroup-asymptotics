import SymmetricSubgroupAsymptotics.C1DegreeNineRankBudget
import SymmetricSubgroupAsymptotics.FusionSourceRestriction
import SymmetricSubgroupAsymptotics.TernaryThreeGroupPhysicalOwner

/-!
# The degree-nine ternary owner from its exact numerical source budget

The sharp degree-nine calculation consumes only
`9*d₃(J) ≤ 2*b+3`.  This file exposes that smaller interface and installs it
in original-weight physical fusion.  The stronger orbit pattern remains one
way to produce the budget, but it is not carried through the numerical proof.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Every quotient of a transitive degree-nine ternary action has binary
slope `8/9` on a source satisfying the exact retained rank budget. -/
theorem degreeNine_rankBudget_quotientEpimorphism_le_binary
    {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hDegree : Nat.card X = 9) (hU : IsPGroup 3 U) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ {Q : Type} [Group Q] [Finite Q]
        (q : U →* Q), Function.Surjective q →
        ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
          C1DegreeNineRankBudget J →
          (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
            constant * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
  obtain ⟨constant, hconstant, hEnvelope⟩ :=
    degreeNine_quotientCharacterEnvelope U hDegree hU
  refine ⟨3 * constant, by positivity, ?_⟩
  intro Q _ _ q hq b J hbudget
  let d := Module.finrank (ZMod 3) (PrimeCharacters 3 J)
  have hbudgetNat : 9 * d ≤ 2 * b + 3 := by
    simpa only [C1DegreeNineRankBudget, Nat.card_fin, d] using hbudget
  have hbudgetR : (9 : ℝ) * (d : ℝ) ≤ 2 * (b : ℝ) + 3 := by
    exact_mod_cast hbudgetNat
  have hexponent : (d : ℝ) + (1 / 3 : ℝ) * b ≤
      1 + (5 / 9 : ℝ) * b := by
    linarith
  calc
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        constant * (3 : ℝ) ^ ((d : ℝ) + (1 / 3 : ℝ) * b) :=
      hEnvelope q hq b J
    _ ≤ constant * (3 : ℝ) ^ (1 + (5 / 9 : ℝ) * b) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) hconstant
    _ = (3 * constant) * (3 : ℝ) ^ ((5 / 9 : ℝ) * b) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      norm_num
      ring
    _ ≤ (3 * constant) * (2 : ℝ) ^
        ((8 / 5 : ℝ) * ((5 / 9 : ℝ) * b)) :=
      mul_le_mul_of_nonneg_left
        (c1_ternary_rpow_envelope (by positivity)) (by positivity)
    _ = (3 * constant) * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
      congr 2
      ring

/-- Original-weight physical degree-nine row under the exact numerical
source-budget bridge. -/
theorem degreeNine_rankBudget_ternaryPGroup_physical_owner_bound
    (U : Subgroup (Equiv.Perm (Fin 9)))
    [MulAction.IsPretransitive U (Fin 9)] (hU : IsPGroup 3 U)
    (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (hSource : ∀ (N : {N : Subgroup U // N.Normal})
      (J : Subgroup (Equiv.Perm (Fin b))) (β : GroupEpimorphism J (U ⧸ N.1)),
      P (fusionFullGoursatEncode N J β).1 →
        C1DegreeNineRankBudget J) :
    ∃ D : ℝ, 0 ≤ D ∧
      (Nat.card (FusionOrbitFamily U
          (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + 9) ≤
        c1EarlierKernel b .degreeNine D
            (Nat.card (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin 9)))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) := by
  obtain ⟨constant, hconstant, hquotient⟩ :=
    degreeNine_rankBudget_quotientEpimorphism_le_binary
      U (by simp) hU
  let D : ℝ := Nat.card {N : Subgroup U // N.Normal} * constant
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hconstant
  refine ⟨D, hD, ?_⟩
  apply c1EarlierPhysical_owner_bound_of_source_direct .degreeNine U b P hP
    C1DegreeNineRankBudget hSource D hD
  intro J hJ
  have haxis (N : {N : Subgroup U // N.Normal}) :
      fusionSurvivingEpiCount U P N J ≤
        constant * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
    have hsub : Nat.card { β : GroupEpimorphism J (U ⧸ N.1) //
        P (fusionFullGoursatEncode N J β).1 } ≤
        Nat.card (GroupEpimorphism J (U ⧸ N.1)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hsubR : fusionSurvivingEpiCount U P N J ≤
        (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := by
      unfold fusionSurvivingEpiCount
      exact_mod_cast hsub
    exact hsubR.trans
      (hquotient (QuotientGroup.mk' N.1)
        (QuotientGroup.mk'_surjective N.1) b J hJ)
  calc
    (∑ N : {N : Subgroup U // N.Normal},
        fusionSurvivingEpiCount U P N J) ≤
        ∑ _N : {N : Subgroup U // N.Normal},
          constant * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) :=
      Finset.sum_le_sum (fun N _ => haxis N)
    _ = D * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card]
      dsimp only [D]
      ring
    _ ≤ D * ((b : ℝ) + 1) *
        (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by
      have hb : (1 : ℝ) ≤ (b : ℝ) + 1 := by
        linarith [Nat.cast_nonneg (α := ℝ) b]
      calc
        D * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) =
            (D * 1) * (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by ring
        _ ≤ (D * ((b : ℝ) + 1)) *
            (2 : ℝ) ^ (((8 : ℝ) / 9) * b) := by gcongr
        _ = _ := by ring
    _ = D * ((b : ℝ) + 1) *
        (2 : ℝ) ^ (c1EarlierExponent .degreeNine * b) := by
      rfl

/-- If the rank budget is part of the source-restricted predicate, the
surviving-map bridge required above is automatic. -/
theorem degreeNine_rankBudget_sourceRestricted_physical_owner_bound
    (U : Subgroup (Equiv.Perm (Fin 9)))
    [MulAction.IsPretransitive U (Fin 9)] (hU : IsPGroup 3 U)
    (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hRestricted : FusionOrbitNatural U
      (FusionSourceRestrictedPredicate U P C1DegreeNineRankBudget)) :
    ∃ D : ℝ, 0 ≤ D ∧
      (Nat.card (FusionOrbitFamily U
          (FusionAcceptedOrbitPredicate U
            (FusionSourceRestrictedPredicate U P
              C1DegreeNineRankBudget))) : ℝ) /
          exactBenchmark (b + 9) ≤
        c1EarlierKernel b .degreeNine D
            (Nat.card (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin 9)))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) := by
  apply degreeNine_rankBudget_ternaryPGroup_physical_owner_bound
    U hU b (FusionSourceRestrictedPredicate U P C1DegreeNineRankBudget)
      hRestricted
  intro N J β h
  exact fusionSourceRestrictedPredicate_encode_source U P
    C1DegreeNineRankBudget N J β h

end SymmetricSubgroupAsymptotics

end
