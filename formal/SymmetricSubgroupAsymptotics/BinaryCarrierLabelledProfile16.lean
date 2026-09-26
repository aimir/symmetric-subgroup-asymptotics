import SymmetricSubgroupAsymptotics.BinaryCarrierMixedProfile16
import SymmetricSubgroupAsymptotics.OrbitProfileUpperWeights

/-! Original labelled profile weights for the literal critical/five-master
model reserve. Physical degree and carrier occurrence count are separate.
The denominator uses only the original action normalizers and the original
occurrence factorials. An arbitrary survival family is also bounded by
literal inclusion in the full family, without asserting its naturality.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierLabelledProfile16

open BinaryCarrierMasterWords16 BinaryCarrierMixedProfile16

variable (p : CriticalProfile) (m : Master → ℕ)

def carrierCount : ℕ := ∑ i, m i

/-- Number of actual labelled points, before any coordinate regrouping. -/
def physicalDegree : ℕ :=
  ∑ i, multiplicity p m i * Fintype.card (points i)

theorem physicalDegree_eq : physicalDegree p m = 2*p.rank + 16*carrierCount m := by
  have h : physicalDegree p m =
      (∑ i, p.multiplicity i * Fintype.card (criticalActionPoints i)) +
        ∑ i, m i * 16 := by
    simp only [physicalDegree, Fintype.sum_sum_type, BinaryCarrierMixedProfile16.multiplicity, points,
      Sum.elim_inl, Sum.elim_inr, Fintype.card_eq_nat_card, Nat.card_fin]
  rw [h, p.physical_degree, ← Finset.sum_mul]
  simp only [carrierCount, Nat.mul_comm]

theorem carrierCount_eq {L : ℕ} (occurrences : Fin L ≃ (Σ i, Fin (m i))) :
    carrierCount m = L := by
  simpa only [carrierCount, Fintype.card_sigma, Fintype.card_fin] using
    (Fintype.card_congr occurrences).symm

theorem physicalDegree_eq_of_enumeration {L : ℕ}
    (occurrences : Fin L ≃ (Σ i, Fin (m i))) :
    physicalDegree p m = 2*p.rank + 16*L := by
  rw [physicalDegree_eq, carrierCount_eq m occurrences]

/-- No containing master or substitute action replaces these normalizers. -/
def originalDenominator : ℝ :=
  ∏ i, (Nat.card (Subgroup.normalizer
    (action i : Set (Equiv.Perm (points i)))) : ℝ) ^ multiplicity p m i *
      (multiplicity p m i).factorial

def labelledBound (L : ℕ) : ℝ :=
  ((physicalDegree p m).factorial : ℝ) * reserve p L / originalDenominator p m

def modelPredicate (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop)
    (K : Subgroup (Equiv.Perm (ModelPoints p m))) : Prop :=
  OrbitProfileFull action 1 K ∧ P K

/-- Naturality of the survival predicate suffices, but the direct bound
below only needs naturality after restricting to the full model family. -/
theorem modelPredicate_natural
    (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop)
    (hP : OrbitProfileFamilyNatural points (multiplicity p m) action P) :
    OrbitProfileFamilyNatural points (multiplicity p m) action (modelPredicate p m P) := by
  intro w hw K hK
  exact ⟨orbitProfileFull_family_natural (multiplicity p m) action w hw K hK.1,
    hP w hw K hK.2⟩

/-- Direct original-weight bound for a natural full survival family on
any actual labelled set. The enumeration records the original occurrences. -/
theorem assembled_survival_card_le_reserve {L : ℕ}
    (occurrences : Fin L ≃ (Σ i, Fin (m i)))
    (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop)
    (hnatural : OrbitProfileFamilyNatural points (multiplicity p m) action
      (modelPredicate p m P))
    {X : Type*} (labels : ModelPoints p m ≃ X) :
    (Nat.card (AssembledOrbitProfileOn (modelPredicate p m P) X) : ℝ) ≤
      labelledBound p m L := by
  have hmodel : (Nat.card {K // modelPredicate p m P K} : ℝ) ≤ reserve p L :=
    modelFamily_card_le_reserve p m occurrences P
  simpa only [labelledBound, physicalDegree, originalDenominator] using
    assembledOrbitProfileOn_card_le_real_of_model_bound hnatural labels hmodel

/-- The complete full model family has automatic joint naturality. -/
theorem assembled_full_card_le_reserve {L : ℕ}
    (occurrences : Fin L ≃ (Σ i, Fin (m i)))
    {X : Type*} (labels : ModelPoints p m ≃ X) :
    (Nat.card (AssembledOrbitProfileOn
      (OrbitProfileFull (m := multiplicity p m) action 1) X) : ℝ) ≤
      labelledBound p m L := by
  have hmodel :
      (Nat.card {K // OrbitProfileFull (m := multiplicity p m) action 1 K} : ℝ) ≤
        reserve p L := by
    simpa only [ModelFamily, and_true] using
      modelFamily_card_le_reserve p m occurrences (fun _ => True)
  simpa only [labelledBound, physicalDegree, originalDenominator] using
    assembledOrbitProfileOn_card_le_real_of_model_bound
      (orbitProfileFull_family_natural (multiplicity p m) action) labels hmodel

/-- The same unconditional bound for literal full physical subgroups,
with their presentations forgotten. -/
theorem full_profile_card_le_reserve {L : ℕ}
    (occurrences : Fin L ≃ (Σ i, Fin (m i)))
    {X : Type*} (labels : ModelPoints p m ≃ X) :
    (Nat.card (FullOrbitProfileOn points (multiplicity p m) action X) : ℝ) ≤
      labelledBound p m L := by
  rw [← Nat.card_congr (assembledFullOrbitProfileEquiv
    (X := X) (m := multiplicity p m) action)]
  exact assembled_full_card_le_reserve p m occurrences labels

/-- Forget only the extra survival condition; the underlying physical
permutation subgroup is unchanged. This inclusion requires no invariance. -/
def forgetSurvival
    (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop) (X : Type*) :
    AssembledOrbitProfileOn (modelPredicate p m P) X ↪
      FullOrbitProfileOn points (multiplicity p m) action X where
  toFun H := ⟨H.1, AssembledOrbitProfileOn.full (fun _ h => h.1) H⟩
  inj' := by
    intro H K h
    apply Subtype.ext
    exact congrArg
      (fun J : FullOrbitProfileOn points (multiplicity p m) action X => J.1) h

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

/-- Even a non-invariant survival family is a literal subfamily of the
whole full profile. This uses the whole-family bound, not a naturality
claim for the survival predicate. -/
theorem arbitrary_survival_card_le_reserve {L : ℕ}
    (occurrences : Fin L ≃ (Σ i, Fin (m i)))
    (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop)
    {X : Type*} (labels : ModelPoints p m ≃ X) :
    (Nat.card (AssembledOrbitProfileOn (modelPredicate p m P) X) : ℝ) ≤
      labelledBound p m L := by
  letI : Finite X := Finite.of_equiv (ModelPoints p m) labels
  letI : Finite (FullOrbitProfileOn points (multiplicity p m) action X) := by
    unfold FullOrbitProfileOn
    infer_instance
  have hcard : Nat.card (AssembledOrbitProfileOn (modelPredicate p m P) X) ≤
      Nat.card (FullOrbitProfileOn points (multiplicity p m) action X) :=
    Nat.card_le_card_of_injective (forgetSurvival p m P X) (forgetSurvival p m P X).injective
  have hreal : (Nat.card (AssembledOrbitProfileOn (modelPredicate p m P) X) : ℝ) ≤
      (Nat.card (FullOrbitProfileOn points (multiplicity p m) action X) : ℝ) := by
    exact_mod_cast hcard
  exact hreal.trans (full_profile_card_le_reserve p m occurrences labels)

end SymmetricSubgroupAsymptotics.BinaryCarrierLabelledProfile16
