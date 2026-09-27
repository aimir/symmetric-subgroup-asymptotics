import SymmetricSubgroupAsymptotics.RepeatedMarkerOrbitProfiles

/-!
# The intrinsic positive-defect original marker family

Membership is stated only in terms of the original subgroup, its literal
orbit images, its counts of singleton and three-point orbits, and an
arbitrary original ownership predicate. The actual orbit chart gives the
degree balance; binary exterior degrees give the even remaining support.
The subgroup is then embedded unchanged into the complete physical profile
family, whose checked ordinary recurrence applies without a counting input.

The explicit Fits condition admits binary orbit images and actual full-S3
orbit images. It makes no claim about other odd actions or zero defect.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerIntrinsicPositive

open RepeatedMarkerOrbitProfiles

/-- The literal binary exterior degree is even after singleton removal. -/
theorem exteriorDegree_even (n : ℕ) (m : BinaryExteriorOrbitMenu.Label n → ℕ) :
    2 ∣ RepeatedMarkerMergedProfile.exteriorDegree (BinaryExteriorOrbitMenu.points n) m :=
  OrbitProfileSingletonExtraction.remainingDegree_even
    (BinaryExteriorOrbitMenu.points n) m (BinaryExteriorOrbitMenu.action n)
    (BinaryExteriorOrbitMenu.action_isPGroup n) (BinaryExteriorOrbitMenu.action_transitive n)
    (BinaryExteriorOrbitMenu.point_card_ne_one n)

/-- The support and complete profile are derived from the actual orbit
chart. No degree balance or full-profile premise is supplied. -/
theorem exists_support_profile (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n)))
    (hfits : Fits H) :
    ∃ r p : ℕ, ∃ m : BinaryExteriorOrbitMenu.Label n → ℕ,
      2*p + RepeatedMarkerMergedProfile.exteriorDegree (BinaryExteriorOrbitMenu.points n) m = 2*r ∧
      RepeatedMarkerAggregateProfile.totalDegree r (orbitCount H 3) (orbitCount H 1) = n ∧
      ∃ e : RepeatedMarkerCompleteProfile.ModelPoints (BinaryExteriorOrbitMenu.points n)
          m p (orbitCount H 3) (orbitCount H 1) ≃ Fin n,
        OrbitProfileFullOn (RepeatedMarkerOrbitProfiles.action n) e H := by
  obtain ⟨p,m,e,he⟩ := exists_complete_profile H n
    (by simpa only [Fintype.card_fin] using (le_rfl : n ≤ n)) hfits
  have hc :
      (∑ i, RepeatedMarkerCompleteProfile.multiplicity m p (orbitCount H 3) (orbitCount H 1) i *
        Fintype.card (RepeatedMarkerCompleteProfile.points (BinaryExteriorOrbitMenu.points n) i)) = n := by
    simpa only [RepeatedMarkerCompleteProfile.ModelPoints,OrbitProfilePoints,
      Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin] using Fintype.card_congr e
  rw [RepeatedMarkerCompleteProfile.degree (BinaryExteriorOrbitMenu.points n)
    m p (orbitCount H 3) (orbitCount H 1)] at hc
  change orbitCount H 1 + (3*orbitCount H 3 +
    (2*p + RepeatedMarkerMergedProfile.exteriorDegree (BinaryExteriorOrbitMenu.points n) m)) = n at hc
  obtain ⟨s,hs⟩ := exteriorDegree_even n m
  refine ⟨p+s,p,m,?_,?_,e,he⟩
  · omega
  · unfold RepeatedMarkerAggregateProfile.totalDegree
    omega

/-- A family of the same original subgroups, with an intrinsic positive
orbit defect and arbitrary retained ownership predicate P. -/
def Family (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :=
  {H : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) //
    Fits H ∧ 1 ≤ (orbitCount H 3 + orbitCount H 1 - epsilon)/2 ∧ P H}

/-- Each intrinsic member enters the exhaustive profile family with its
literal subgroup value unchanged. -/
theorem exists_positive (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop)
    (H : Family N epsilon P) :
    ∃ K : BinaryExteriorOrbitMenu.PositiveFamily N epsilon P, K.1 = H.1 := by
  obtain ⟨r,p,m,hsize,hn,e,he⟩ := exists_support_profile (2*N+epsilon) H.1 H.2.1
  exact RepeatedMarkerPositiveFamily.contains_original_profile
    (BinaryExteriorOrbitMenu.points (2*N+epsilon)) (BinaryExteriorOrbitMenu.action (2*N+epsilon))
    N epsilon r (orbitCount H.1 3) (orbitCount H.1 1) p m hn H.2.2.1 hsize P
    ⟨H.1,⟨e,he⟩⟩ H.2.2.2

def toPositive (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop)
    (H : Family N epsilon P) : BinaryExteriorOrbitMenu.PositiveFamily N epsilon P :=
  Classical.choose (exists_positive N epsilon P H)

@[simp] theorem toPositive_val (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) (H : Family N epsilon P) :
    (toPositive N epsilon P H).1 = H.1 :=
  Classical.choose_spec (exists_positive N epsilon P H)

def embedding (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :
    Family N epsilon P ↪ BinaryExteriorOrbitMenu.PositiveFamily N epsilon P where
  toFun := toPositive N epsilon P
  inj' := by
    intro H K h
    apply Subtype.ext
    exact (toPositive_val N epsilon P H).symm.trans
      ((congrArg Subtype.val h).trans (toPositive_val N epsilon P K))

local instance positiveFamilyFinite (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :
    Finite (BinaryExteriorOrbitMenu.PositiveFamily N epsilon P) :=
  Finite.of_injective
    (fun H : BinaryExteriorOrbitMenu.PositiveFamily N epsilon P =>
      (H.1 : Set (Equiv.Perm (Fin (2*N+epsilon)))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

theorem card_le_positive (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :
    Nat.card (Family N epsilon P) ≤ Nat.card (BinaryExteriorOrbitMenu.PositiveFamily N epsilon P) :=
  Nat.card_le_card_of_injective (embedding N epsilon P) (embedding N epsilon P).injective

/-- The complete intrinsic positive-defect count enters the strictly
forward ordinary row. There is no supplied profile, action-menu coverage,
count inequality, or bounded-target assumption. -/
theorem positive_card_div_benchmark_le (N epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :
    (Nat.card (Family N epsilon P) : ℝ) / exactBenchmark (2*N+epsilon) ≤
      ∑ m ∈ Finset.range (2*N+epsilon),
        MarkerDegreeForwardRow.kernel (2*N+epsilon) m * ordinarySubgroupRatio m := by
  have hc : (Nat.card (Family N epsilon P) : ℝ) ≤
      Nat.card (BinaryExteriorOrbitMenu.PositiveFamily N epsilon P) := by
    exact_mod_cast card_le_positive N epsilon P
  exact (div_le_div_of_nonneg_right hc (exactBenchmark_pos _).le).trans
    (BinaryExteriorOrbitMenu.positive_card_div_benchmark_le N epsilon hepsilon P)

end SymmetricSubgroupAsymptotics.RepeatedMarkerIntrinsicPositive

end
