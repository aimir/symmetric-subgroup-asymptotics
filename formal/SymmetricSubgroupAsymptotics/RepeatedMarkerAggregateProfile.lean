import SymmetricSubgroupAsymptotics.RepeatedMarkerCompleteProfile
import SymmetricSubgroupAsymptotics.RepeatedMarkerMergedProfileSum
import SymmetricSubgroupAsymptotics.RepeatedMarkerOrdinaryTarget
import SymmetricSubgroupAsymptotics.MarkerMergedFactorial

/-!
# Original fixed-parameter marker families and one ordinary target per width

The source is the actual union of complete original profiles, with any
ownership restriction on their literal permutation subgroups. Its count
is bounded through the proved singleton and marker cover. At fixed q the
merged profile recovers every original exterior multiplicity, so all
target profiles share one ordinary subgroup count. No local or global
subgroup-cardinality estimate is supplied as a hypothesis.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerAggregateProfile

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

abbrev Profile := RepeatedMarkerMergedProfileSum.Profile (α := α)
def totalDegree (r g f : ℕ) : ℕ := f + (3*g + 2*r)
def targetDegree (r q : ℕ) : ℕ := 2*(r+q)

abbrev Source (r g f : ℕ) (t : Profile (α := α)) :=
  RepeatedMarkerCompleteProfile.Family Ω t.2 U t.1 g f (Fin (totalDegree r g f))

abbrev RestrictedSource (r g f : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (totalDegree r g f))) → Prop) (t : Profile (α := α)) :=
  {H : Source Ω U r g f t // P H.1}

/-- A literal original family: the profile and chart are existential
witnesses, not extra objects included in its cardinality. -/
def Family (r g f : ℕ) (S : Finset (Profile (α := α)))
    (P : Subgroup (Equiv.Perm (Fin (totalDegree r g f))) → Prop) :=
  {H : Subgroup (Equiv.Perm (Fin (totalDegree r g f))) //
    ∃ t : S, ∃ K : RestrictedSource Ω U r g f P t.1, K.1.1 = H}

theorem card_family_le_sum (r g f : ℕ) (S : Finset (Profile (α := α)))
    (P : Subgroup (Equiv.Perm (Fin (totalDegree r g f))) → Prop) :
    Nat.card (Family Ω U r g f S P) ≤
      ∑ t : S, Nat.card (RestrictedSource Ω U r g f P t.1) := by
  letI : ∀ t : S, Finite (RestrictedSource Ω U r g f P t.1) := fun t => by
    unfold RestrictedSource Source RepeatedMarkerCompleteProfile.Family FullOrbitProfileOn
    infer_instance
  let decode : (Σ t : S, RestrictedSource Ω U r g f P t.1) → Family Ω U r g f S P :=
    fun z => ⟨z.2.1.1,z.1,z.2,rfl⟩
  have hd : Function.Surjective decode := by
    rintro ⟨H,t,K,hK⟩
    exact ⟨⟨t,K⟩,Subtype.ext hK⟩
  calc
    _ ≤ Nat.card (Σ t : S, RestrictedSource Ω U r g f P t.1) :=
      Nat.card_le_card_of_surjective decode hd
    _ = _ := Nat.card_sigma

/-- The original pair/exterior support equation supplies both actual
point charts. It is a degree identity, not a counting hypothesis. -/
def sourceChart (r g f : ℕ) (t : Profile (α := α))
    (ht : 2*t.1 + RepeatedMarkerMergedProfile.exteriorDegree Ω t.2 = 2*r) :
    RepeatedMarkerCompleteProfile.ModelPoints Ω t.2 t.1 g f ≃ Fin (totalDegree r g f) :=
  orbitProfileFinLabels (RepeatedMarkerCompleteProfile.points Ω)
    (RepeatedMarkerCompleteProfile.multiplicity t.2 t.1 g f) _ (by
      rw [RepeatedMarkerCompleteProfile.degree]
      unfold RepeatedMarkerCompleteProfile.sourceDegree totalDegree
      rw [ht])

def targetChart (r q : ℕ) (t : Profile (α := α))
    (ht : 2*t.1 + RepeatedMarkerMergedProfile.exteriorDegree Ω t.2 = 2*r) :
    RepeatedMarkerMergedProfile.ModelPoints Ω t.2 (q+t.1) ≃ Fin (targetDegree r q) :=
  orbitProfileFinLabels (RepeatedMarkerMergedProfile.points Ω)
    (RepeatedMarkerMergedProfile.multiplicity t.2 (q+t.1)) _ (by
      rw [RepeatedMarkerMergedProfile.degree]
      unfold targetDegree
      omega)

theorem collapsed_card_eq (r q : ℕ) (t : Profile (α := α))
    (ht : 2*t.1 + RepeatedMarkerMergedProfile.exteriorDegree Ω t.2 = 2*r) :
    Nat.card (RepeatedMarkerFixedProfileBound.CollapsedFamily Ω t.2 U t.1 q) =
      Nat.card (RepeatedMarkerMergedProfileSum.Family Ω U q (targetDegree r q) t) := by
  let P := OrbitProfileReindexedProduct.modelPredicate
    (RepeatedMarkerMergedProfile.multiplicity t.2 (q+t.1))
    (RepeatedMarkerMergedProfile.action Ω U) (fun _ => True)
  exact Nat.card_congr
    ((assembledOrbitProfileEquivOn P (Equiv.refl _)).symm.trans
      (assembledOrbitProfileEquivOn P (targetChart Ω r q t ht)))

def coefficient (r g f q : ℕ) : ℚ :=
  ((totalDegree r g f).factorial : ℚ) / (targetDegree r q).factorial *
    ((2 : ℚ)^q * RepeatedMarkerAllocationWeights.markerProfileSum (Q := Fin q) g /
      ((6 : ℚ)^g * f.factorial)) * ((r+q).descFactorial q : ℚ)

theorem coefficient_nonneg (r g f q : ℕ) : 0 ≤ coefficient r g f q := by
  have hH := RepeatedMarkerOrdinaryTarget.markerProfileSum_nonneg g q
  unfold coefficient
  positivity

/-- Each original profile is bounded using the actual checked cover,
then the unchanged pair factorial is enlarged monotonically. -/
theorem source_card_le (r g f : ℕ) (t : Profile (α := α))
    (ht : 2*t.1 + RepeatedMarkerMergedProfile.exteriorDegree Ω t.2 = 2*r)
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegreeOne : ∀ a, Fintype.card (Ω a) ≠ 1)
    (hdegreeTwo : ∀ a, Fintype.card (Ω a) ≠ 2)
    (P : Subgroup (Equiv.Perm (Fin (totalDegree r g f))) → Prop) :
    (Nat.card (RestrictedSource Ω U r g f P t) : ℚ) ≤
      ∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
        coefficient r g f q.1 *
          (Nat.card (RepeatedMarkerMergedProfileSum.Family Ω U q.1 (targetDegree r q.1) t) : ℚ) := by
  have h := RepeatedMarkerCompleteProfile.card_restricted_le Ω t.2 U t.1 g f
    (sourceChart Ω r g f t ht) hU htrans hsep hdegreeOne hdegreeTwo P
  apply h.trans
  apply Finset.sum_le_sum
  intro q _
  have hs : RepeatedMarkerCompleteProfile.sourceDegree Ω t.2 t.1 g f = totalDegree r g f := by
    unfold RepeatedMarkerCompleteProfile.sourceDegree totalDegree
    rw [ht]
  have hd : 2*(q.1+t.1) + RepeatedMarkerMergedProfile.exteriorDegree Ω t.2 = targetDegree r q.1 := by
    unfold targetDegree
    omega
  rw [hs,hd,collapsed_card_eq Ω U r q.1 t ht]
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left
    (show (((q.1+t.1).factorial : ℚ) / t.1.factorial) ≤ ((r+q.1).descFactorial q.1 : ℚ) from by
      rw [Nat.add_comm q.1 t.1]
      exact MarkerMergedFactorial.ratio_le_descFactorial t.1 q.1 (r+q.1) (by omega))
  have hH := RepeatedMarkerOrdinaryTarget.markerProfileSum_nonneg g q.1
  positivity

/-- Actual union bound followed by disjoint merged-profile summation.
There is one ordinary target per retained width, not per exterior profile. -/
theorem card_family_le (r g f : ℕ) (S : Finset (Profile (α := α)))
    (hsize : ∀ t ∈ S, 2*t.1 + RepeatedMarkerMergedProfile.exteriorDegree Ω t.2 = 2*r)
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegreeOne : ∀ a, Fintype.card (Ω a) ≠ 1)
    (hdegreeTwo : ∀ a, Fintype.card (Ω a) ≠ 2)
    (P : Subgroup (Equiv.Perm (Fin (totalDegree r g f))) → Prop) :
    (Nat.card (Family Ω U r g f S P) : ℚ) ≤
      ∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
        coefficient r g f q.1 * (subgroupCount (targetDegree r q.1) : ℚ) := by
  have hc : (Nat.card (Family Ω U r g f S P) : ℚ) ≤
      ∑ t : S, (Nat.card (RestrictedSource Ω U r g f P t.1) : ℚ) := by
    exact_mod_cast card_family_le_sum Ω U r g f S P
  apply hc.trans
  calc
    _ ≤ ∑ t : S, ∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
        coefficient r g f q.1 *
          (Nat.card (RepeatedMarkerMergedProfileSum.Family Ω U q.1 (targetDegree r q.1) t.1) : ℚ) := by
      apply Finset.sum_le_sum
      intro t _
      exact source_card_le Ω U r g f t.1 (hsize t.1 t.2)
        hU htrans hsep hdegreeOne hdegreeTwo P
    _ = ∑ q : RepeatedMarkerPresentationSum.Width (ι := Fin g),
        coefficient r g f q.1 *
          ∑ t : S, (Nat.card (RepeatedMarkerMergedProfileSum.Family Ω U q.1 (targetDegree r q.1) t.1) : ℚ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (coefficient_nonneg r g f q.1)
      have hc := RepeatedMarkerMergedProfileSum.sum_card_le_subgroupCount Ω U
        q.1 (targetDegree r q.1) S htrans hsep hdegreeTwo
      rw [← Finset.sum_coe_sort S (fun t =>
        Nat.card (RepeatedMarkerMergedProfileSum.Family Ω U q.1 (targetDegree r q.1) t))] at hc
      exact_mod_cast hc

/-- Every width in a profile with markers or fixed points is forward.
The all-empty g=f=0 profile is deliberately excluded. -/
theorem target_lt_total (r g f q : ℕ) (hpositive : 0 < g+f) (hq : q ≤ g) :
    targetDegree r q < totalDegree r g f := by
  unfold targetDegree totalDegree
  omega

end SymmetricSubgroupAsymptotics.RepeatedMarkerAggregateProfile

end
