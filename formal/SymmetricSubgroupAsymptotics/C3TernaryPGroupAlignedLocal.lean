import SymmetricSubgroupAsymptotics.C3PhysicalOwnerAlignedContinuation
import SymmetricSubgroupAsymptotics.TernaryThreeGroupRankBudgetOwner

/-!
# Ternary p-group rows on aligned high-C3 cells

The aligned continuation remembers the exact selected action.  This file
attaches the two valid ternary p-group rows to that action: degree twenty
seven unconditionally, and degree nine after the exact numerical source
budget has been retained in the local predicate.  The degree-three action is
not assigned a numerical row here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The degree-nine subcell retains the original first-owner predicate and
the exact rank budget on its whole undeleted source. -/
def c3HighAlignedRankBudgetPredicate
    (j : C3HighAlignedFirstOwnerIndex) (b : ℕ) :
    Subgroup (c3HighAlignedFirstOwnerAction j ×
      Equiv.Perm (Fin b)) → Prop :=
  FusionSourceRestrictedPredicate
    (c3HighAlignedFirstOwnerAction j)
    (c3HighAlignedFirstOwnerPredicate j b)
    C1DegreeNineRankBudget

/-- The rank budget is conjugacy invariant, so the restricted aligned cell is
an original-normalizer-natural physical family without an extra bridge. -/
theorem c3HighAlignedRankBudgetPredicate_natural
    (j : C3HighAlignedFirstOwnerIndex) (b : ℕ) :
    FusionOrbitNatural (c3HighAlignedFirstOwnerAction j)
      (c3HighAlignedRankBudgetPredicate j b) := by
  exact fusionSourceRestrictedPredicate_natural
    (c3HighAlignedFirstOwnerAction j)
    (c3HighAlignedFirstOwnerPredicate j b)
    C1DegreeNineRankBudget
    (c3HighAlignedFirstOwnerPredicate_natural j b)
    (fun c J h => C1DegreeNineRankBudget.map_conj J h c)

/-- An aligned ternary p-group cell of width twenty seven has the complete
unrestricted original-weight row on its literal selected action. -/
theorem c3HighAligned_degreeTwentySeven_local_bound
    (owner : Fin 4)
    (i : Non2TransitiveActionClass (Fin 27))
    (hj : C3HighAlignedOwnerAction
      (c3PhysicalOwnerKindEquiv owner) i.representative)
    (hkind : c3PhysicalOwnerKindEquiv owner =
      C3PhysicalOwnerKind.ternaryPGroup)
    (n : ℕ) (hn : 27 ≤ n) :
    ∃ D : ℝ, 0 ≤ D ∧
      (Nat.card (FusionWidthCanonicalFamily
        i.representative hn
        (c3HighFirstOwnerPredicate
          ⟨C3HighWidthLabel.twentySeven, owner, i⟩ (n - 27))) : ℝ) /
          exactBenchmark n ≤
        c1EarlierKernel (n - 27) .degreeTwentySeven D
            (Nat.card (Subgroup.normalizer
              (i.representative : Set (Equiv.Perm (Fin 27)))) : ℝ) *
          ordinarySubgroupRatio (n - 27) := by
  have hU := hj.2
  rw [hkind] at hU
  let b := n - 27
  obtain ⟨D, hD, hmain⟩ :=
    degreeTwentySeven_ternaryPGroup_physical_owner_bound
      i.representative hU b
      (c3HighFirstOwnerPredicate
        ⟨C3HighWidthLabel.twentySeven, owner, i⟩ b)
      (c3HighFirstOwnerPredicate_natural
        ⟨C3HighWidthLabel.twentySeven, owner, i⟩ b)
  refine ⟨D, hD, ?_⟩
  rw [fusionWidthCanonicalFamily_card]
  have hbn : b + 27 = n := Nat.sub_add_cancel hn
  simpa only [b, hbn, ordinarySubgroupRatio] using hmain

/-- An aligned ternary p-group cell of width nine has the sharp row once the
retained numerical source budget is installed in the cell itself. -/
theorem c3HighAligned_degreeNine_rankBudget_local_bound
    (owner : Fin 4)
    (i : Non2TransitiveActionClass (Fin 9))
    (hj : C3HighAlignedOwnerAction
      (c3PhysicalOwnerKindEquiv owner) i.representative)
    (hkind : c3PhysicalOwnerKindEquiv owner =
      C3PhysicalOwnerKind.ternaryPGroup)
    (n : ℕ) (hn : 9 ≤ n) :
    ∃ D : ℝ, 0 ≤ D ∧
      (Nat.card (FusionWidthCanonicalFamily
        i.representative hn
        (FusionSourceRestrictedPredicate i.representative
          (c3HighFirstOwnerPredicate
            ⟨C3HighWidthLabel.nine, owner, i⟩ (n - 9))
          C1DegreeNineRankBudget)) : ℝ) /
          exactBenchmark n ≤
        c1EarlierKernel (n - 9) .degreeNine D
            (Nat.card (Subgroup.normalizer
              (i.representative : Set (Equiv.Perm (Fin 9)))) : ℝ) *
          ordinarySubgroupRatio (n - 9) := by
  have hU := hj.2
  rw [hkind] at hU
  let b := n - 9
  have hRestricted : FusionOrbitNatural i.representative
      (FusionSourceRestrictedPredicate i.representative
        (c3HighFirstOwnerPredicate
          ⟨C3HighWidthLabel.nine, owner, i⟩ b)
        C1DegreeNineRankBudget) :=
    c3HighAlignedRankBudgetPredicate_natural
      ⟨⟨C3HighWidthLabel.nine, owner, i⟩, hj⟩ b
  obtain ⟨D, hD, hmain⟩ :=
    degreeNine_rankBudget_sourceRestricted_physical_owner_bound
      i.representative hU b
      (c3HighFirstOwnerPredicate
        ⟨C3HighWidthLabel.nine, owner, i⟩ b) hRestricted
  refine ⟨D, hD, ?_⟩
  rw [fusionWidthCanonicalFamily_card]
  have hbn : b + 9 = n := Nat.sub_add_cancel hn
  simpa only [b, hbn, ordinarySubgroupRatio] using hmain

end SymmetricSubgroupAsymptotics

end
