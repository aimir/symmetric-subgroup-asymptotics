import SymmetricSubgroupAsymptotics.OrbitProfileOrbitCriterion
import SymmetricSubgroupAsymptotics.BinaryFamilies

/-!
# Intrinsic criticality of the original even permutation subgroup

The complete four-action critical family includes every full lift. It is
therefore characterized by the exact images on the original orbits. There
is no canonical-kernel condition, abstract-isomorphism substitution, or
counting premise. The orbit condition itself excludes singleton orbits
and forces even degree. Odd critical families, which permit one singleton
or one full-S3 marker, are deliberately not identified with this condition.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.CriticalOrbitCriterion

variable {X : Type*} (H : Subgroup (Equiv.Perm X))

/-- Every literal orbit action is one of the four original critical
permutation actions, with its full image retained. -/
def AllCriticalOrbits : Prop :=
  ∀ o : OrbitProfileFromOrbits.Orbit H, ∃ i : CriticalActionKind,
    ∃ e : criticalActionPoints i ≃ o.orbit,
      relabelSubgroup e (criticalActionSubgroup i) = OrbitProfileFromOrbits.orbitImage H o

def profileOfMultiplicity (m : CriticalActionKind → ℕ) : CriticalProfile :=
  ⟨m .c2,m .v4,m .d8,m .e8⟩

@[simp] theorem profileOfMultiplicity_multiplicity (m : CriticalActionKind → ℕ) :
    (profileOfMultiplicity m).multiplicity = m := by
  funext i
  cases i <;> rfl

/-- A simultaneous original chart is constructed from the local images;
conversely every full critical chart recovers those same original images. -/
theorem exists_critical_profile_iff [Finite X] :
    (∃ p : CriticalProfile, ∃ e : OrbitProfilePoints criticalActionPoints p.multiplicity ≃ X,
      OrbitProfileFullOn criticalActionSubgroup e H) ↔ AllCriticalOrbits H := by
  constructor
  · rintro ⟨p,e,he⟩
    exact (OrbitProfileFromOrbits.exists_profile_iff_orbit_images H
      criticalActionSubgroup criticalAction_transitive).mp ⟨p.multiplicity,e,he⟩
  · intro h
    obtain ⟨m,e,he⟩ := (OrbitProfileFromOrbits.exists_profile_iff_orbit_images H
      criticalActionSubgroup criticalAction_transitive).mpr h
    refine ⟨profileOfMultiplicity m,?_⟩
    rw [profileOfMultiplicity_multiplicity]
    exact ⟨e,he⟩

/-- The original degree is forced by its critical orbit images. -/
theorem degree_of_allCriticalOrbits [Fintype X] (h : AllCriticalOrbits H) :
    ∃ p : CriticalProfile, 2*p.rank = Fintype.card X ∧
      ∃ e : OrbitProfilePoints criticalActionPoints p.multiplicity ≃ X,
        OrbitProfileFullOn criticalActionSubgroup e H := by
  obtain ⟨p,e,he⟩ := (exists_critical_profile_iff H).mpr h
  refine ⟨p,?_,e,he⟩
  have hc : (∑ i, p.multiplicity i * Fintype.card (criticalActionPoints i)) =
      Fintype.card X := by
    simpa only [OrbitProfilePoints,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
      using Fintype.card_congr e
  rwa [p.physical_degree] at hc

/-- Singleton orbits cannot be smuggled into the even critical criterion. -/
theorem hasNoFixedPoints_of_allCriticalOrbits [Finite X] (h : AllCriticalOrbits H) :
    HasNoFixedPoints H := by
  obtain ⟨p,e,he⟩ := (exists_critical_profile_iff H).mpr h
  exact he.hasNoFixedPoints criticalAction_moves_point

/-- Exact iff for the existing complete even critical family. Neither
binaryity nor fixed-point-freeness is a supplied premise. -/
theorem isEvenCritical_iff (N : ℕ) (H : Subgroup (Equiv.Perm (Fin (2*N)))) :
    IsEvenCriticalSubgroup N H ↔ AllCriticalOrbits H := by
  constructor
  · rintro ⟨p,e,K,hK,hKH⟩
    have hfull : ∃ c : OrbitProfilePoints criticalActionPoints p.val.multiplicity ≃ Fin (2*N),
        OrbitProfileFullOn criticalActionSubgroup c H :=
      AssembledOrbitProfileOn.full (fun _ h => h) ⟨H,e,K,hK,hKH⟩
    obtain ⟨c,hc⟩ := hfull
    exact (exists_critical_profile_iff H).mp ⟨p.val,c,hc⟩
  · intro h
    obtain ⟨p,hp,e,he⟩ := degree_of_allCriticalOrbits H h
    have hrank : p.rank = N := by
      rw [Fintype.card_fin] at hp
      omega
    refine ⟨⟨p,(mem_criticalProfiles N p).mpr hrank⟩,
      e,relabelSubgroup e.symm H,?_,relabelSubgroup_symm e.symm H⟩
    apply (orbitProfileFullOn_iff criticalActionSubgroup 1 _).mp
    have ht := he.relabel e.symm
    simpa only [Equiv.self_trans_symm] using ht

/-- Failure of complete criticality is witnessed by an actual original
orbit whose full action is not any of the four critical actions. -/
theorem not_isEvenCritical_iff (N : ℕ) (H : Subgroup (Equiv.Perm (Fin (2*N)))) :
    (¬ IsEvenCriticalSubgroup N H) ↔
      ∃ o : OrbitProfileFromOrbits.Orbit H,
        ¬ ∃ i : CriticalActionKind, ∃ e : criticalActionPoints i ≃ o.orbit,
          relabelSubgroup e (criticalActionSubgroup i) = OrbitProfileFromOrbits.orbitImage H o := by
  rw [isEvenCritical_iff,AllCriticalOrbits,not_forall]

/-- This even-orbit condition is false in odd degree. A separate odd
criterion must retain its permitted singleton or S3 marker. -/
theorem not_allCriticalOrbits_odd (N : ℕ)
    (H : Subgroup (Equiv.Perm (Fin (2*N+1)))) : ¬ AllCriticalOrbits H := by
  intro h
  obtain ⟨p,hp,_,_⟩ := degree_of_allCriticalOrbits H h
  rw [Fintype.card_fin] at hp
  omega

end SymmetricSubgroupAsymptotics.CriticalOrbitCriterion

end
