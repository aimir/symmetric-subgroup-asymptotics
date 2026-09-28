import SymmetricSubgroupAsymptotics.TernaryThreeGroupEpiRecurrence
import SymmetricSubgroupAsymptotics.C1OwnerAggregate

/-!
# Physical owners for bounded ternary actions

The quotient recursion is attached to the original-weight physical count.
Degree twenty seven is unconditional.  Degree nine retains the precise
one-regular-`C3`/no-natural-`A4` source predicate and therefore cannot be
applied to an enlarged canonical cell without a separate source bridge.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Direct source-restricted form of the original-weight consumer.  When the
source predicate fails, every surviving original Goursat map is empty by the
stated structural bridge. -/
theorem c1EarlierPhysical_owner_bound_of_source_direct
    (r : C1EarlierRow)
    (U : Subgroup (Equiv.Perm (Fin (c1EarlierWidth r)))) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (Source : Subgroup (Equiv.Perm (Fin b)) → Prop)
    (hSource : ∀ (N : {N : Subgroup U // N.Normal})
      (J : Subgroup (Equiv.Perm (Fin b))) (β : GroupEpimorphism J (U ⧸ N.1)),
      P (fusionFullGoursatEncode N J β).1 → Source J)
    (D : ℝ) (hD : 0 ≤ D)
    (hsource : ∀ J : Subgroup (Equiv.Perm (Fin b)), Source J →
      (∑ N : {N : Subgroup U // N.Normal},
        fusionSurvivingEpiCount U P N J) ≤
          D * ((b : ℝ) + 1) *
            (2 : ℝ) ^ (c1EarlierExponent r * b)) :
    (Nat.card (FusionOrbitFamily U
        (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + c1EarlierWidth r) ≤
      c1EarlierKernel b r D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin (c1EarlierWidth r))))) : ℝ) *
        ((subgroupCount b : ℝ) / exactBenchmark b) := by
  apply c1EarlierPhysical_owner_bound r U b P hP D
  intro J
  by_cases hJ : Source J
  · exact hsource J hJ
  · have hz (N : {N : Subgroup U // N.Normal}) :
        fusionSurvivingEpiCount U P N J = 0 := by
      letI : IsEmpty { β : GroupEpimorphism J (U ⧸ N.1) //
          P (fusionFullGoursatEncode N J β).1 } :=
        ⟨fun f => hJ (hSource N J f.1 f.2)⟩
      simp only [fusionSurvivingEpiCount, Nat.card_of_isEmpty, Nat.cast_zero]
    rw [Finset.sum_eq_zero (fun N _ => hz N)]
    positivity

/-- Every full physical family based on a transitive degree-twenty-seven
ternary group has the unconditional `.degreeTwentySeven` original-weight
row.  The constant is finite and depends only on the retained action. -/
theorem degreeTwentySeven_ternaryPGroup_physical_owner_bound
    (U : Subgroup (Equiv.Perm (Fin 27)))
    [MulAction.IsPretransitive U (Fin 27)] (hU : IsPGroup 3 U)
    (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P) :
    ∃ D : ℝ, 0 ≤ D ∧
      (Nat.card (FusionOrbitFamily U
          (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + 27) ≤
        c1EarlierKernel b .degreeTwentySeven D
            (Nat.card (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin 27)))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) := by
  obtain ⟨constant, hconstant, hquotient⟩ :=
    degreeTwentySeven_quotientEpimorphism_le_binary
      U (by simp) hU
  let D : ℝ :=
    Nat.card {N : Subgroup U // N.Normal} * constant
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hconstant
  refine ⟨D, hD, ?_⟩
  apply c1EarlierPhysical_owner_bound .degreeTwentySeven U b P hP D
  intro J
  have haxis (N : {N : Subgroup U // N.Normal}) :
      fusionSurvivingEpiCount U P N J ≤
        constant * (2 : ℝ) ^ (((8 : ℝ) / 3) * b) := by
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
        (QuotientGroup.mk'_surjective N.1) b J)
  calc
    (∑ N : {N : Subgroup U // N.Normal},
        fusionSurvivingEpiCount U P N J) ≤
        ∑ _N : {N : Subgroup U // N.Normal},
          constant * (2 : ℝ) ^ (((8 : ℝ) / 3) * b) :=
      Finset.sum_le_sum (fun N _ => haxis N)
    _ = D * (2 : ℝ) ^ (((8 : ℝ) / 3) * b) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card]
      dsimp only [D]
      ring
    _ ≤ D * ((b : ℝ) + 1) *
        (2 : ℝ) ^ (((8 : ℝ) / 3) * b) := by
      have hb : (1 : ℝ) ≤ (b : ℝ) + 1 := by
        linarith [Nat.cast_nonneg (α := ℝ) b]
      calc
        D * (2 : ℝ) ^ (((8 : ℝ) / 3) * b) =
            (D * 1) * (2 : ℝ) ^ (((8 : ℝ) / 3) * b) := by ring
        _ ≤ (D * ((b : ℝ) + 1)) *
            (2 : ℝ) ^ (((8 : ℝ) / 3) * b) := by gcongr
        _ = _ := by ring
    _ = D * ((b : ℝ) + 1) *
        (2 : ℝ) ^ (c1EarlierExponent .degreeTwentySeven * b) := by
      rfl

/-- The marked degree-nine physical row.  Its structural premise is exactly
the missing bridge from each surviving complete physical map to the retained
source pattern; no broader cell is assigned the `8/9` exponent. -/
theorem degreeNine_marked_ternaryPGroup_physical_owner_bound
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (U : Subgroup (Equiv.Perm (Fin 9)))
    [MulAction.IsPretransitive U (Fin 9)] (hU : IsPGroup 3 U)
    (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (hSource : ∀ (N : {N : Subgroup U // N.Normal})
      (J : Subgroup (Equiv.Perm (Fin b))) (β : GroupEpimorphism J (U ⧸ N.1)),
      P (fusionFullGoursatEncode N J β).1 →
        C1DegreeNineSourcePattern J) :
    ∃ D : ℝ, 0 ≤ D ∧
      (Nat.card (FusionOrbitFamily U
          (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + 9) ≤
        c1EarlierKernel b .degreeNine D
            (Nat.card (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin 9)))) : ℝ) *
          ((subgroupCount b : ℝ) / exactBenchmark b) := by
  obtain ⟨constant, hconstant, hquotient⟩ :=
    degreeNine_marked_quotientEpimorphism_le_binary
      hChief hPrimitive h18 U (by simp) hU
  let D : ℝ :=
    Nat.card {N : Subgroup U // N.Normal} * constant
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hconstant
  refine ⟨D, hD, ?_⟩
  apply c1EarlierPhysical_owner_bound_of_source_direct .degreeNine U b P hP
    C1DegreeNineSourcePattern hSource D hD
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

end SymmetricSubgroupAsymptotics

end
