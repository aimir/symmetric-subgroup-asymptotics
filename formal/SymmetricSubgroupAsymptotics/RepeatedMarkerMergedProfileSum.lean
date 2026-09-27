import SymmetricSubgroupAsymptotics.RepeatedMarkerMergedProfile
import SymmetricSubgroupAsymptotics.Statements

/-!
# One ordinary target count for all distinct merged exterior profiles

At a fixed retained width q, the merged multiplicity vector records p+q
and every original exterior multiplicity. It therefore recovers the
entire original pair/exterior profile. The full physical families on the
same actual labelled set are disjoint. Summing their cardinalities costs
one complete ordinary subgroup count, rather than one such count per
exterior profile. No restriction on the number of profiles is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerMergedProfileSum

open RepeatedMarkerMergedProfile

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

/-- The actual old pair count and the complete exterior multiplicity
function; neither is discarded or replaced by a count of labels. -/
abbrev Profile := ℕ × (α → ℕ)

def mergedMultiplicity (q : ℕ) (t : Profile (α := α)) : PUnit.{1} ⊕ α → ℕ :=
  RepeatedMarkerMergedProfile.multiplicity t.2 (q+t.1)

theorem mergedMultiplicity_injective (q : ℕ) :
    Function.Injective (mergedMultiplicity (α := α) q) := by
  intro t s h
  apply Prod.ext
  · have hp := congrFun h (.inl PUnit.unit)
    change q+t.1 = q+s.1 at hp
    exact Nat.add_left_cancel hp
  · funext a
    exact congrFun h (.inr a)

abbrev Family (q d : ℕ) (t : Profile (α := α)) :=
  OrbitProfileReindexedProduct.PhysicalFamily (mergedMultiplicity q t) (action Ω U)
    (fun _ => True) (Fin d)

/-- Forgetting the profile gives an injection, because actual orbits
recover the merged vector and cancellation recovers the original vector. -/
def profileEmbedding (q d : ℕ) (S : Finset (Profile (α := α)))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Σ t : S, Family Ω U q d t.1) ↪ Subgroup (Equiv.Perm (Fin d)) where
  toFun z := z.2.1
  inj' := by
    rintro ⟨t,H⟩ ⟨s,K⟩ h
    have he : mergedMultiplicity q t.1 = mergedMultiplicity q s.1 :=
      assembledOrbitProfileOn_disjoint (fun _ hK => hK.1) (fun _ hK => hK.1)
        (action_transitive Ω U htrans) (action_separated Ω U hsep hdegree) H K h
    have hts : t = s := Subtype.ext (mergedMultiplicity_injective q he)
    subst s
    have hHK : H = K := Subtype.ext h
    subst K
    rfl

/-- All exterior profiles share one complete ordinary target. Profiles
of the wrong degree simply have an empty physical family. -/
theorem sum_card_le_subgroupCount (q d : ℕ) (S : Finset (Profile (α := α)))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (∑ t ∈ S, Nat.card (Family Ω U q d t)) ≤ subgroupCount d := by
  letI : ∀ t : S, Finite (Family Ω U q d t.1) := fun t => by
    unfold Family OrbitProfileReindexedProduct.PhysicalFamily AssembledOrbitProfileOn
    infer_instance
  have h := Nat.card_le_card_of_injective (profileEmbedding Ω U q d S htrans hsep hdegree)
    (profileEmbedding Ω U q d S htrans hsep hdegree).injective
  rw [Nat.card_sigma] at h
  change (∑ t : S, Nat.card (Family Ω U q d t.1)) ≤ subgroupCount d at h
  rwa [Finset.sum_coe_sort S (fun t => Nat.card (Family Ω U q d t))] at h

/-- A uniform coefficient bound may be taken outside the complete
profile sum. There is no multiplier counting exterior profiles. -/
theorem weighted_sum_le (q d : ℕ) (S : Finset (Profile (α := α)))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2)
    (w : Profile (α := α) → ℚ) (B : ℚ) (hB : 0 ≤ B)
    (hw : ∀ t ∈ S, w t ≤ B) :
    (∑ t ∈ S, w t * (Nat.card (Family Ω U q d t) : ℚ)) ≤
      B * (subgroupCount d : ℚ) := by
  calc
    _ ≤ ∑ t ∈ S, B * (Nat.card (Family Ω U q d t) : ℚ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_right (hw t ht) (Nat.cast_nonneg _)
    _ = B * ∑ t ∈ S, (Nat.card (Family Ω U q d t) : ℚ) :=
      (Finset.mul_sum S _ B).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast sum_card_le_subgroupCount Ω U q d S htrans hsep hdegree) hB

end SymmetricSubgroupAsymptotics.RepeatedMarkerMergedProfileSum

end
