import SymmetricSubgroupAsymptotics.BinaryOriginalNoncriticalPhysical
import SymmetricSubgroupAsymptotics.BinaryDegreeEightNormalizerSaturatedDirect
import SymmetricSubgroupAsymptotics.BinaryDegree16NormalizerSaturatedDirect
import SymmetricSubgroupAsymptotics.BinaryS16PositiveResidualEstimate

/-!
# Intrinsic four-owner partition of the binary error family

Every noncritical fixed-point-free binary subgroup is assigned, without a
mark, to the first of: an orbit of width at least 32, a direct degree-eight
owner, a direct degree-sixteen owner, or the positive S16 residual.  The last
branch is positive because its zero-support alternative is precisely the
excluded complete critical family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryNativeOwnerPartition

open SymmetricSubgroupAsymptotics

abbrev Owner (N : ℕ) :=
  BinaryOriginalNoncriticalPhysical.physicalFamily (2*N) ⊕
    (BinaryDegreeEightNormalizerSaturatedDirect.directFamily (2*N) ⊕
      (BinaryDegree16PhysicalAnalyticClosure.directFamily (2*N) ⊕
        BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N))

def underlying {N : ℕ} : Owner N → Subgroup (Equiv.Perm (Fin (2*N)))
  | .inl H => H.1
  | .inr (.inl H) => H.1
  | .inr (.inr (.inl H)) => H.1
  | .inr (.inr (.inr H)) => H.1.1

private theorem orbitImage_binary {N : ℕ} (H : NoncriticalBinarySubgroups N)
    (x : Fin (2*N)) :
    IsPGroup 2 (FusionActualOrbitCharts.orbitImage H.1 x) := by
  exact H.2.1.1.of_surjective
    (PermutationCharacterRankSplit.restrictionHom
      (FusionActualOrbitCharts.orbitSet H.1 x)).rangeRestrict
    (PermutationCharacterRankSplit.restrictionHom
      (FusionActualOrbitCharts.orbitSet H.1 x)).rangeRestrict_surjective

private theorem orbit_le_sixteen_of_not_wide {N : ℕ}
    (H : NoncriticalBinarySubgroups N)
    (hwide : H.1 ∉ BinaryOriginalNoncriticalPhysical.physicalFamily (2*N))
    (o : OrbitProfileFromOrbits.Orbit H.1) : Nat.card o.orbit ≤ 16 := by
  have hP := orbitImage_binary H o.out
  have hlt : Nat.card (MulAction.orbit H.1 o.out) < 32 := by
    by_contra h
    apply hwide
    exact ⟨o.out,by omega,hP⟩
  obtain ⟨k,hk⟩ :=
    BinaryOriginalLargePhysical.orbit_card_eq_two_pow H.1 o.out hP
  have hk5 : k<5 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
    simpa only [hk,show (2:ℕ)^5=32 from rfl] using hlt
  have horbit : Nat.card o.orbit = Nat.card (MulAction.orbit H.1 o.out) := by
    rw [o.orbit_eq_orbit_out Quotient.out_eq']
  rw [horbit,hk]
  interval_cases k <;> norm_num at hk5 ⊢

/-- Deterministic first-owner assignment of every member of the binary error
family. -/
def owner {N : ℕ} (H : NoncriticalBinarySubgroups N) : Owner N := by
  by_cases hwide : H.1 ∈ BinaryOriginalNoncriticalPhysical.physicalFamily (2*N)
  · exact .inl ⟨H.1,hwide⟩
  by_cases h8 : H.1 ∈ BinaryDegreeEightNormalizerSaturatedDirect.directFamily (2*N)
  · exact .inr (.inl ⟨H.1,h8⟩)
  by_cases h16 : H.1 ∈ BinaryDegree16PhysicalAnalyticClosure.directFamily (2*N)
  · exact .inr (.inr (.inl ⟨H.1,h16⟩))
  let hres : BinaryS16CanonicalCarrierProfile.ResidualSector H.1 :=
    { binary := H.2.1.1
      noFixedPoints := H.2.1.2
      orbit_le := orbit_le_sixteen_of_not_wide H hwide
      noDirect8 := h8
      noDirect16 := h16 }
  have hpositive : 0 < BinaryS16JointOrbitData.oldSupport H.1 hres := by
    rcases BinaryS16DirectResidualPartition.directPositive_or_isEvenCritical
      H.1 hres with hp | hc
    · exact hp
    · exact False.elim (H.2.2 hc)
  exact .inr (.inr (.inr ⟨⟨H.1,hres⟩,hpositive⟩))

@[simp] theorem underlying_owner {N : ℕ} (H : NoncriticalBinarySubgroups N) :
    underlying (owner H) = H.1 := by
  unfold owner
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem owner_injective {N : ℕ} : Function.Injective (owner (N := N)) := by
  intro H K h
  apply Subtype.ext
  calc
    H.1 = underlying (owner H) := (underlying_owner H).symm
    _ = underlying (owner K) := congrArg underlying h
    _ = K.1 := underlying_owner K

theorem card_le_owners (N : ℕ) :
    Nat.card (NoncriticalBinarySubgroups N) ≤
      Nat.card (BinaryOriginalNoncriticalPhysical.physicalFamily (2*N)) +
      Nat.card (BinaryDegreeEightNormalizerSaturatedDirect.directFamily (2*N)) +
      Nat.card (BinaryDegree16PhysicalAnalyticClosure.directFamily (2*N)) +
      Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) := by
  calc
    Nat.card (NoncriticalBinarySubgroups N) ≤ Nat.card (Owner N) :=
      Nat.card_le_card_of_injective owner owner_injective
    _ = _ := by simp only [Owner,Nat.card_sum]; omega

end SymmetricSubgroupAsymptotics.BinaryNativeOwnerPartition
