import SymmetricSubgroupAsymptotics.RepeatedMarkerPositiveParameters

/-!
# The actual complete positive-defect marker family

Every natural support triple and every compatible exterior multiplicity
profile is included. All witnesses are forgotten on the same original
Fin n subgroup. The physical upper bound is derived from the checked
profile cover and the injective support-to-parameter map; no subgroup
count, numerical envelope, or bounded ordinary ratio is assumed.

The exterior action menu is any finite separated family of the actual
binary transitive actions of degree different from one and two. Its
exhaustiveness for a larger owner sector is a separate action-coverage
question; within this menu the support and multiplicity families are
complete, and arbitrary original ownership predicates are retained.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerPositiveFamily

open RepeatedMarkerPositiveParameters MarkerGeometry MarkerNormalizedKernel

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

def supportChart {N epsilon : ℕ} (s : Support N epsilon) :
    Fin (RepeatedMarkerAggregateProfile.totalDegree s.r s.g s.f) ≃ Fin (2*N+epsilon) :=
  finCongr s.balance

abbrev LocalFamily {N epsilon : ℕ}
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) (s : Support N epsilon) :=
  RepeatedMarkerAggregateProfile.Family Ω U s.r s.g s.f (profiles Ω s.r)
    (fun H => P (relabelSubgroup (supportChart s) H))

/-- The support and original profile are existential witnesses. Only the
same original ambient permutation subgroup is counted. -/
def Family (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :=
  {H : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) //
    ∃ s : Support N epsilon, ∃ K : LocalFamily Ω U P s,
      relabelSubgroup (supportChart s) K.1 = H}

local instance localFamilyFinite {N epsilon : ℕ}
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) (s : Support N epsilon) :
    Finite (LocalFamily Ω U P s) :=
  Finite.of_injective (fun K : LocalFamily Ω U P s => K.1) Subtype.val_injective

/-- Every natural support/profile instance belongs to the complete
family; the finite parameter boxes impose no additional restriction. -/
theorem contains_original_profile (N epsilon r g f p : ℕ) (m : α → ℕ)
    (hn : RepeatedMarkerAggregateProfile.totalDegree r g f = 2*N+epsilon)
    (hD : 1 ≤ (g+f-epsilon)/2)
    (hsize : 2*p + RepeatedMarkerMergedProfile.exteriorDegree Ω m = 2*r)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop)
    (H : RepeatedMarkerCompleteProfile.Family Ω m U p g f (Fin (2*N+epsilon)))
    (hP : P H.1) : ∃ K : Family Ω U N epsilon P, K.1 = H.1 := by
  let s : Support N epsilon := Support.ofNat N epsilon r g f hn hD
  let e := supportChart s
  let L : RepeatedMarkerCompleteProfile.Family Ω m U p g f
      (Fin (RepeatedMarkerAggregateProfile.totalDegree r g f)) :=
    ⟨relabelSubgroup e.symm H.1,by
      obtain ⟨c,hc⟩ := H.2
      exact ⟨c.trans e.symm,hc.relabel e.symm⟩⟩
  have hLP : P (relabelSubgroup e L.1) := by
    change P (relabelSubgroup e (relabelSubgroup e.symm H.1))
    have he : relabelSubgroup e (relabelSubgroup e.symm H.1) = H.1 :=
      relabelSubgroup_symm e.symm H.1
    rw [he]
    exact hP
  let K : LocalFamily Ω U P s :=
    ⟨L.1,⟨⟨(p,m),(mem_profiles Ω r (p,m)).mpr hsize⟩,⟨L,hLP⟩,rfl⟩⟩
  refine ⟨⟨H.1,s,K,?_⟩,rfl⟩
  change relabelSubgroup e (relabelSubgroup e.symm H.1) = H.1
  exact relabelSubgroup_symm e.symm H.1

/-- Conversely, the family retains the actual ownership predicate and
an original full profile with its complete degree and defect identities. -/
theorem original_profile {N epsilon : ℕ}
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop)
    (H : Family Ω U N epsilon P) :
    P H.1 ∧ ∃ r g f p : ℕ, ∃ m : α → ℕ,
      RepeatedMarkerAggregateProfile.totalDegree r g f = 2*N+epsilon ∧
      1 ≤ (g+f-epsilon)/2 ∧
      2*p + RepeatedMarkerMergedProfile.exteriorDegree Ω m = 2*r ∧
      ∃ c : RepeatedMarkerCompleteProfile.ModelPoints Ω m p g f ≃ Fin (2*N+epsilon),
        OrbitProfileFullOn (RepeatedMarkerCompleteProfile.action Ω U) c H.1 := by
  obtain ⟨s,K,hKH⟩ := H.2
  obtain ⟨t,L,hLK⟩ := K.2
  have hgroup : relabelSubgroup (supportChart s) L.1.1 = H.1 :=
    (congrArg (relabelSubgroup (supportChart s)) hLK).trans hKH
  constructor
  · have hP := L.2
    change P (relabelSubgroup (supportChart s) L.1.1) at hP
    rwa [hgroup] at hP
  · obtain ⟨c,hc⟩ := L.1.2
    refine ⟨s.r,s.g,s.f,t.1.1,t.1.2,s.balance,s.positive,
      profiles_size Ω s.r t.1 t.2,c.trans (supportChart s),?_⟩
    have h := hc.relabel (supportChart s)
    rwa [hgroup] at h

theorem card_le_support_sum (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :
    Nat.card (Family Ω U N epsilon P) ≤
      ∑ s : Support N epsilon, Nat.card (LocalFamily Ω U P s) := by
  let decode : (Σ s : Support N epsilon, LocalFamily Ω U P s) → Family Ω U N epsilon P :=
    fun z => ⟨relabelSubgroup (supportChart z.1) z.2.1,z.1,z.2,rfl⟩
  have hd : Function.Surjective decode := by
    rintro ⟨H,s,K,hK⟩
    exact ⟨⟨s,K⟩,Subtype.ext hK⟩
  calc
    _ ≤ Nat.card (Σ s : Support N epsilon, LocalFamily Ω U P s) :=
      Nat.card_le_card_of_surjective decode hd
    _ = _ := Nat.card_sigma

local instance defectFibreFinite (N epsilon D : ℕ) : Finite (DefectFibre N epsilon D) :=
  Finite.of_injective profileCode profileCode_injective

local instance defectFibreFintype (N epsilon D : ℕ) : Fintype (DefectFibre N epsilon D) :=
  Fintype.ofFinite _

/-- The complete actual positive-defect family is bounded by the complete
actual weighted parameter row. Exterior profiles and support triples are
not charged separately to the same ordinary target. -/
theorem card_div_benchmark_le (N epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegreeOne : ∀ a, Fintype.card (Ω a) ≠ 1)
    (hdegreeTwo : ∀ a, Fintype.card (Ω a) ≠ 2)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :
    (Nat.card (Family Ω U N epsilon P) : ℝ) / exactBenchmark (2*N+epsilon) ≤
      ∑ D ∈ Finset.Icc 1 N, ∑ s : DefectFibre N epsilon D,
        profileKernel s.1 * ordinarySubgroupRatio (2*s.1.M) := by
  have hc : (Nat.card (Family Ω U N epsilon P) : ℝ) ≤
      ∑ s : Support N epsilon, (Nat.card (LocalFamily Ω U P s) : ℝ) := by
    exact_mod_cast card_le_support_sum Ω U N epsilon P
  apply (div_le_div_of_nonneg_right hc (exactBenchmark_pos _).le).trans
  rw [Finset.sum_div]
  calc
    _ ≤ ∑ s : Support N epsilon, ∑ q : RepeatedMarkerNormalizedProfile.AdmissibleWidth s.g,
        profileKernel (RepeatedMarkerNormalizedProfile.parameter
          N epsilon s.r s.g s.f hepsilon s.balance q) *
          ordinarySubgroupRatio (2*(s.r+q.1.1)) := by
      apply Finset.sum_le_sum
      intro s _
      exact RepeatedMarkerNormalizedProfile.card_family_div_benchmark_le Ω U
        N epsilon s.r s.g s.f hepsilon s.balance (profiles Ω s.r) (profiles_size Ω s.r)
        hU htrans hsep hdegreeOne hdegreeTwo
        (fun H => P (relabelSubgroup (supportChart s) H))
    _ = ∑ z : Occurrence N epsilon,
        profileKernel (parameterOfOccurrence N epsilon hepsilon z) *
          ordinarySubgroupRatio (2*(parameterOfOccurrence N epsilon hepsilon z).M) := by
      rw [Fintype.sum_sigma]
      rfl
    _ ≤ _ := sum_occurrences_le N epsilon hepsilon
      (fun s => profileKernel s * ordinarySubgroupRatio (2*s.M))
      (fun s => mul_nonneg (profileKernel_nonneg s) (ordinarySubgroupRatio_nonneg _))

end SymmetricSubgroupAsymptotics.RepeatedMarkerPositiveFamily

end
