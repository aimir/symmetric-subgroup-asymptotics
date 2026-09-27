import SymmetricSubgroupAsymptotics.RepeatedMarkerIntrinsicPositive
import SymmetricSubgroupAsymptotics.FiniteProductPGroup
import SymmetricSubgroupAsymptotics.NoncriticalBinaryOrdinary

/-!
# The intrinsic zero-defect marker branch

The complete `Fits` family splits literally into positive orbit defect and
zero orbit defect.  The degree parity forces a zero-defect profile to have
exactly the parity marker count.  At even degree this removes every
singleton and every full `S3` orbit.  The original subgroup is therefore a
fixed-point-free `2`-group, and an ordinary subgroup enters the existing
noncritical binary owner without changing its value.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerZeroDefect

open RepeatedMarkerOrbitProfiles

def FullFamily (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :=
  {H : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) // Fits H ∧ P H}

def Family (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :=
  {H : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) //
    Fits H ∧ (orbitCount H 3 + orbitCount H 1 - epsilon)/2 = 0 ∧ P H}

local instance finiteSubgroupPredicate (n : ℕ)
    (Q : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    Finite {H : Subgroup (Equiv.Perm (Fin n)) // Q H} :=
  Finite.of_injective
    (fun H : {K : Subgroup (Equiv.Perm (Fin n)) // Q K} =>
      (H.1 : Set (Equiv.Perm (Fin n))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

/-- Exact exhaustive partition before counting: the complementary branch
to positive intrinsic defect is literal zero defect. -/
def partitionEquiv (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :
    FullFamily N epsilon P ≃
      RepeatedMarkerIntrinsicPositive.Family N epsilon P ⊕ Family N epsilon P where
  toFun H := by
    by_cases h : 1 ≤ (orbitCount H.1 3 + orbitCount H.1 1 - epsilon)/2
    · exact .inl ⟨H.1,H.2.1,h,H.2.2⟩
    · exact .inr ⟨H.1,H.2.1,Nat.eq_zero_of_not_pos h,H.2.2⟩
  invFun H := match H with
    | .inl K => ⟨K.1,K.2.1,K.2.2.2⟩
    | .inr K => ⟨K.1,K.2.1,K.2.2.2⟩
  left_inv H := by
    by_cases h : 1 ≤ (orbitCount H.1 3 + orbitCount H.1 1 - epsilon)/2
    · simp [h]
    · simp [h]
  right_inv H := by
    rcases H with H | H
    · have h := H.2.2.1
      simp [h]
    · have hzero := H.2.2.1
      have hnot : ¬ 1 ≤ (orbitCount H.1 3 + orbitCount H.1 1 - epsilon)/2 := by
        omega
      simp [hnot]

theorem card_partition (N epsilon : ℕ)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop) :
    Nat.card (FullFamily N epsilon P) =
      Nat.card (RepeatedMarkerIntrinsicPositive.Family N epsilon P) +
        Nat.card (Family N epsilon P) := by
  letI : Finite (RepeatedMarkerIntrinsicPositive.Family N epsilon P) :=
    Finite.of_injective
      (fun H : RepeatedMarkerIntrinsicPositive.Family N epsilon P =>
        (H.1 : Set (Equiv.Perm (Fin (2*N+epsilon)))))
      (fun _ _ h => Subtype.ext (SetLike.coe_injective h))
  letI : Finite (Family N epsilon P) :=
    Finite.of_injective
      (fun H : Family N epsilon P =>
        (H.1 : Set (Equiv.Perm (Fin (2*N+epsilon)))))
      (fun _ _ h => Subtype.ext (SetLike.coe_injective h))
  rw [Nat.card_congr (partitionEquiv N epsilon P),Nat.card_sum]

/-- In degree `2*N+epsilon`, parity plus zero quotient defect forces the
sum of actual singleton and full-`S3` orbit counts to equal `epsilon`. -/
theorem marker_fixed_eq_epsilon (N epsilon : ℕ) (hepsilon : epsilon ≤ 1)
    (P : Subgroup (Equiv.Perm (Fin (2*N+epsilon))) → Prop)
    (H : Family N epsilon P) :
    orbitCount H.1 3 + orbitCount H.1 1 = epsilon := by
  obtain ⟨r,p,m,hsize,hdegree,e,he⟩ :=
    RepeatedMarkerIntrinsicPositive.exists_support_profile (2*N+epsilon) H.1 H.2.1
  have hzero := H.2.2.1
  unfold RepeatedMarkerAggregateProfile.totalDegree at hdegree
  omega

theorem orbit_card_ne_of_count_eq_zero {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) {d : ℕ} (hzero : orbitCount H d = 0)
    (o : OrbitProfileFromOrbits.Orbit H) : Nat.card o.orbit ≠ d := by
  intro ho
  letI : Nonempty {q : OrbitProfileFromOrbits.Orbit H // Nat.card q.orbit = d} :=
    ⟨⟨o,ho⟩⟩
  have hpos : 0 < orbitCount H d := by
    unfold orbitCount
    exact Nat.card_pos
  omega

/-- With no three-point orbit, the alternative full-`S3` clause in `Fits`
is impossible, so every actual restriction image is a `2`-group. -/
theorem orbitImage_isPGroup_of_marker_count_zero {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) (hfits : Fits H) (hmarker : orbitCount H 3 = 0)
    (o : OrbitProfileFromOrbits.Orbit H) :
    IsPGroup 2 (OrbitProfileFromOrbits.orbitImage H o) := by
  rcases hfits o with hp | ⟨e,he⟩
  · exact hp
  · exfalso
    apply orbit_card_ne_of_count_eq_zero H hmarker o
    calc
      Nat.card o.orbit = Nat.card (Fin 3) := (Nat.card_congr e).symm
      _ = 3 := by simp

/-- Simultaneous faithful restriction to all actual orbits shows that a
`Fits` subgroup with no full-`S3` orbit is itself a `2`-group. -/
theorem isPGroup_of_marker_count_zero {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) (hfits : Fits H) (hmarker : orbitCount H 3 = 0) :
    IsPGroup 2 H := by
  letI : Fintype (OrbitProfileFromOrbits.Orbit H) := Fintype.ofFinite _
  let U : (o : OrbitProfileFromOrbits.Orbit H) → Subgroup (Equiv.Perm o.orbit) :=
    fun o => OrbitProfileFromOrbits.orbitImage H o
  let C : OrbitProfileFromOrbits.Data H U :=
    { label := fun o => o
      pointEquiv := fun o => Equiv.refl o.orbit
      image_eq := fun o => by simp [U] }
  apply C.chart_full.isPGroup_of_occupied
  intro o ho
  exact orbitImage_isPGroup_of_marker_count_zero H hfits hmarker o

/-- Zero singleton count is the intrinsic fixed-point-free condition.  The
proof uses the original orbit action and does not select representatives. -/
theorem hasNoFixedPoints_of_fixed_count_zero {X : Type} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) (hfixed : orbitCount H 1 = 0) :
    HasNoFixedPoints H := by
  letI : Fintype (OrbitProfileFromOrbits.Orbit H) := Fintype.ofFinite _
  let U : (o : OrbitProfileFromOrbits.Orbit H) → Subgroup (Equiv.Perm o.orbit) :=
    fun o => OrbitProfileFromOrbits.orbitImage H o
  let C : OrbitProfileFromOrbits.Data H U :=
    { label := fun o => o
      pointEquiv := fun o => Equiv.refl o.orbit
      image_eq := fun o => by simp [U] }
  apply C.chart_full.hasNoFixedPoints
  intro o x
  letI : Nonempty o.orbit := ⟨x⟩
  have hne : Nat.card o.orbit ≠ 1 := orbit_card_ne_of_count_eq_zero H hfixed o
  have hlt : 1 < Fintype.card o.orbit := by
    rw [← Nat.card_eq_fintype_card]
    have hpos : 0 < Nat.card o.orbit := Nat.card_pos
    omega
  letI : Nontrivial o.orbit := Fintype.one_lt_card_iff_nontrivial.mp hlt
  obtain ⟨y,hy⟩ := exists_ne x
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq H x y
  refine ⟨⟨MulAction.toPermHom H o.orbit h,⟨h,rfl⟩⟩,?_⟩
  change h • x ≠ x
  rwa [hh]

theorem even_isFixedPointFreeBinary (N : ℕ)
    (H : Family N 0 (fun K => ¬ IsCriticalSubgroup (2*N) K)) :
    IsFixedPointFreeBinary H.1 := by
  have hsum := marker_fixed_eq_epsilon N 0 (by omega)
    (fun K => ¬ IsCriticalSubgroup (2*N) K) H
  have hm : orbitCount H.1 3 = 0 := by omega
  have hf : orbitCount H.1 1 = 0 := by omega
  exact ⟨isPGroup_of_marker_count_zero H.1 H.2.1 hm,
    hasNoFixedPoints_of_fixed_count_zero H.1 hf⟩

theorem even_notCritical (N : ℕ)
    (H : Family N 0 (fun K => ¬ IsCriticalSubgroup (2*N) K)) :
    ¬ IsEvenCriticalSubgroup N H.1 := by
  intro hcritical
  apply H.2.2.2
  let J : EvenCriticalSubgroups N := ⟨H.1,hcritical⟩
  exact (isCriticalSubgroup_even_iff N H.1).mpr ⟨J,rfl⟩

/-- The even zero-defect branch enters the already existing noncritical
binary owner with the physical subgroup unchanged. -/
def evenEmbedding (N : ℕ) :
    Family N 0 (fun K => ¬ IsCriticalSubgroup (2*N) K) ↪
      NoncriticalBinarySubgroups N where
  toFun H := ⟨H.1,even_isFixedPointFreeBinary N H,even_notCritical N H⟩
  inj' := by
    intro H K h
    apply Subtype.ext
    exact congrArg (fun L : NoncriticalBinarySubgroups N => L.1) h

theorem even_card_le_noncriticalBinary (N : ℕ) :
    Nat.card (Family N 0 (fun K => ¬ IsCriticalSubgroup (2*N) K)) ≤
      Nat.card (NoncriticalBinarySubgroups N) :=
  Nat.card_le_card_of_injective (evenEmbedding N) (evenEmbedding N).injective

end SymmetricSubgroupAsymptotics.RepeatedMarkerZeroDefect

end
