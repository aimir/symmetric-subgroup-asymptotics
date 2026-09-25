import SymmetricSubgroupAsymptotics.CriticalActionModels
import SymmetricSubgroupAsymptotics.OrbitProfileAssembly
import SymmetricSubgroupAsymptotics.OrbitProfileProduct
import SymmetricSubgroupAsymptotics.CriticalProfiles

/-!
# Exact labelled counts for the concrete four-action profiles

The previously enumerated multiplicities and rational profile weights are
installed in actual subgroup families on `Fin n`. The model fibre remains
the literal full subgroup type; no Gaussian count is assumed for it.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The concrete four-colour multiplicity function of a profile. -/
def CriticalProfile.multiplicity (p : CriticalProfile) : CriticalActionKind → ℕ
  | .c2 => p.c2 | .v4 => p.v4 | .d8 => p.d8 | .e8 => p.e8

theorem CriticalProfile.multiplicity_injective : Function.Injective CriticalProfile.multiplicity := by
  intro p q h
  have ha := congrFun h CriticalActionKind.c2
  have hv := congrFun h CriticalActionKind.v4
  have hb := congrFun h CriticalActionKind.d8
  have he := congrFun h CriticalActionKind.e8
  cases p
  cases q
  simp only [multiplicity] at ha hv hb he
  cases ha; cases hv; cases hb; cases he
  rfl

private theorem criticalActionKind_univ : (Finset.univ : Finset CriticalActionKind) =
    {.c2, .v4, .d8, .e8} := by decide

theorem CriticalProfile.physical_degree (p : CriticalProfile) :
    ∑ i, p.multiplicity i * Fintype.card (criticalActionPoints i) = 2 * p.rank := by
  simp only [criticalAction_point_card, criticalActionKind_univ]
  simp [multiplicity, criticalActionDegree, rank]
  omega

theorem CriticalProfile.original_normalizer_weight (p : CriticalProfile) :
    (∏ i, (Nat.card (Subgroup.normalizer (criticalActionSubgroup i : Set (Equiv.Perm (criticalActionPoints i)))) : ℚ) ^
      p.multiplicity i * (p.multiplicity i).factorial)⁻¹ = p.weight := by
  simp only [criticalAction_normalizer_card, criticalActionKind_univ]
  simp [multiplicity, criticalActionNormalizerOrder, weight, one_div, mul_assoc]

/-- Full model subgroups on the original disjoint union of critical blocks. -/
abbrev CriticalModelSubgroups (p : CriticalProfile) :=
  {H : Subgroup (Equiv.Perm (OrbitProfilePoints criticalActionPoints p.multiplicity)) //
    OrbitProfileFull criticalActionSubgroup 1 H}

/-- The actual critical subgroups with this multiplicity profile, on the
usual labelled points. -/
abbrev CriticalProfileSubgroups (p : CriticalProfile) :=
  FullOrbitProfileOn criticalActionPoints p.multiplicity criticalActionSubgroup (Fin (2 * p.rank))

/-- Exact normalizer-weighted count for each concrete critical profile. -/
theorem criticalProfileSubgroups_card (p : CriticalProfile) :
    (Nat.card (CriticalProfileSubgroups p) : ℚ) =
      ((2 * p.rank).factorial : ℚ) * p.weight * Nat.card (CriticalModelSubgroups p) := by
  have h := fullOrbitProfileOn_fin_card_rat p.multiplicity criticalActionSubgroup
    (2 * p.rank) p.physical_degree criticalAction_transitive criticalAction_types_separated
  change _ = _ at h
  rw [h, div_eq_mul_inv, p.original_normalizer_weight]
  ring

/-- The literal union of all four-action profiles at rank `R`, on `Fin (2R)`.
Membership records existence of a full action chart, not a numerical weight. -/
abbrev EvenCriticalSubgroups (R : ℕ) :=
  AssembledOrbitProfilesOn
    (fun p : (criticalProfiles R) ↦ p.1.multiplicity)
    (fun p ↦ OrbitProfileFull (m := p.1.multiplicity) criticalActionSubgroup 1)
    (Fin (2 * R))

/-- The complete even critical family is a disjoint sum of the concrete
model counts with the exact previously defined profile weights. -/
theorem evenCriticalSubgroups_card (R : ℕ) :
    (Nat.card (EvenCriticalSubgroups R) : ℚ) =
      ((2 * R).factorial : ℚ) *
        ∑ p : (criticalProfiles R), p.1.weight * Nat.card (CriticalModelSubgroups p.1) := by
  have hn (p : (criticalProfiles R)) :
      ∑ i, p.1.multiplicity i * Fintype.card (criticalActionPoints i) = 2 * R := by
    rw [p.1.physical_degree, (mem_criticalProfiles R p.1).mp p.2]
  have hm : Function.Injective (fun p : (criticalProfiles R) ↦ p.1.multiplicity) := by
    intro p q h
    exact Subtype.ext (CriticalProfile.multiplicity_injective h)
  have h := assembledOrbitProfilesOn_fin_card_rat
    (m := fun p : (criticalProfiles R) ↦ p.1.multiplicity)
    (P := fun p ↦ OrbitProfileFull (m := p.1.multiplicity) criticalActionSubgroup 1)
    (2 * R) hn hm (fun _ _ h ↦ h)
    (fun p ↦ orbitProfileFull_family_natural p.1.multiplicity criticalActionSubgroup)
    criticalAction_transitive criticalAction_types_separated
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [div_eq_mul_inv, p.1.original_normalizer_weight]
  ring

/-- The literal permutation-model fibre is the full subgroup family of the
independent original-action product, via the faithful block action. -/
def criticalModelSubgroupsEquivProduct (p : CriticalProfile) :
    CriticalModelSubgroups p ≃
      {H : Subgroup (OrbitProfileProductGroup p.multiplicity criticalActionSubgroup) //
        OrbitProfileProductFull p.multiplicity criticalActionSubgroup H} :=
  (orbitProfileProductFullEquiv p.multiplicity criticalActionSubgroup).symm

/-- Exact labelled profile count with the actual direct-product subgroup
fibre exposed, ready for the canonical and noncanonical lift estimates. -/
theorem criticalProfileSubgroups_card_product (p : CriticalProfile) :
    (Nat.card (CriticalProfileSubgroups p) : ℚ) =
      ((2 * p.rank).factorial : ℚ) * p.weight *
        Nat.card {H : Subgroup (OrbitProfileProductGroup p.multiplicity criticalActionSubgroup) //
          OrbitProfileProductFull p.multiplicity criticalActionSubgroup H} := by
  rw [criticalProfileSubgroups_card, Nat.card_congr (criticalModelSubgroupsEquivProduct p)]

/-- The concrete full-product version of the complete even-profile sum. -/
theorem evenCriticalSubgroups_card_product (R : ℕ) :
    (Nat.card (EvenCriticalSubgroups R) : ℚ) =
      ((2 * R).factorial : ℚ) * ∑ p : (criticalProfiles R), p.1.weight *
        Nat.card {H : Subgroup (OrbitProfileProductGroup p.1.multiplicity criticalActionSubgroup) //
          OrbitProfileProductFull p.1.multiplicity criticalActionSubgroup H} := by
  rw [evenCriticalSubgroups_card]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.card_congr (criticalModelSubgroupsEquivProduct p.1)]

end SymmetricSubgroupAsymptotics
