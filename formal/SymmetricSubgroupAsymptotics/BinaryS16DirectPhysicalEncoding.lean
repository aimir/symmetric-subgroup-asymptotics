import SymmetricSubgroupAsymptotics.BinaryS16CanonicalMixedBlockTable
import SymmetricSubgroupAsymptotics.BinaryS16DirectPhysicalTarget

/-!
# The concrete mixed physical key for one direct S16 support fibre

The direct certified orbit profile supplies both pieces of the final bounded
key.  Its positive degree-eight and degree-sixteen routes give the canonical
mixed block table, while its complete correlated source gives the
fusion-natural original-label target.

This file performs only the two exact old-support casts and packages the
remaining reconstruction statement in its smallest concrete form.  The final
chart-varying decoder need only show that equality of these two keys forces
equality of the underlying literal permutation subgroups.  All subtype
proofs, key-fibre subsingleton arguments, and `K = 10` counting consequences
are discharged here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryS16DirectPhysicalEncoding

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierParameterProfiles
open BinaryDegreeEightSixteenPhysicalDecoration
open BinaryDegreeEightSixteenPhysicalEncoding
open BinaryS16DirectFixedSupportClosure

variable {N : ℕ} (C : SupportIndex N)

abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

/-- The mixed table before identifying the direct old support with the fixed
support index. -/
def rawBlocks (H : Actual C) :
    CanonicalMixedBlockTable N
      (BinaryS16JointOrbitData.oldSupport
        (BinaryS16DirectPhysicalTarget.subgroup C H)
        (BinaryS16DirectPhysicalTarget.residualSector C H)) :=
  BinaryS16CanonicalMixedBlockTable.table
    (BinaryS16DirectPhysicalTarget.subgroup C H)
    (BinaryS16DirectPhysicalTarget.residualSector C H)

/-- The canonical mixed block table in the literal fixed-support fibre. -/
def blocks (H : Actual C) : CanonicalMixedBlockTable N C.1.1 :=
  cast
    (congrArg (CanonicalMixedBlockTable N)
      (BinaryS16DirectPhysicalTarget.oldSupport_eq C H))
    (rawBlocks C H)

/-- The concrete table/physical-target key. -/
def physicalKey (H : Actual C) :
    CanonicalMixedBlockTable N C.1.1 × Target N C.1.1 :=
  (blocks C H, BinaryS16DirectPhysicalTarget.target C H)

/-- Forget the retained-bin and profile witnesses and keep the literal
physical subgroup on the original ambient labels. -/
def targetSubgroup (H : Actual C) :
    Subgroup (Equiv.Perm (Fin (2 * N))) :=
  relabelSubgroup
    (Equiv.cast (congrArg (fun M : ℕ ↦ Fin (2 * M))
      (BinaryS16DirectPhysicalTarget.parameter_eq C H)))
    (BinaryS16DirectPhysicalTarget.rawTarget C H).2.1

/-- Equality of the literal permutation subgroup is enough to identify two
elements of the fixed-support fibre; all residual and support witnesses are
proof-valued. -/
theorem actual_ext {H K : Actual C}
    (h : BinaryS16DirectPhysicalTarget.subgroup C H =
      BinaryS16DirectPhysicalTarget.subgroup C K) :
    H = K := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- The smallest concrete chart-varying reflection obligation left to the
physical decoder.  It refers only to the two keys already charged in the
count and asks for equality of the original labelled subgroups.

In particular, no equality of the dependent orbit indices, route words,
quotient types, or point charts appears in the public interface. -/
def ReflectsPhysicalKey : Prop :=
  ∀ ⦃H K : Actual C⦄,
    blocks C H = blocks C K →
    BinaryS16DirectPhysicalTarget.target C H =
      BinaryS16DirectPhysicalTarget.target C K →
    BinaryS16DirectPhysicalTarget.subgroup C H =
      BinaryS16DirectPhysicalTarget.subgroup C K

/-- The still smaller interface expected from the chart-varying incidence
argument.  Once the mixed table is fixed, equality of the two literal target
subgroups must reflect equality of the two literal source subgroups.

This is the useful decoder boundary: it forgets proof-valued profile data and
the retained numerical bin, while keeping the original labels on which the
mixed records are written. -/
def ReflectsTargetSubgroup : Prop :=
  ∀ ⦃H K : Actual C⦄,
    blocks C H = blocks C K →
    targetSubgroup C H = targetSubgroup C K →
    BinaryS16DirectPhysicalTarget.subgroup C H =
      BinaryS16DirectPhysicalTarget.subgroup C K

/-- Literal target-subgroup reflection implies reflection of the complete
retained-bin target key. -/
theorem reflectsPhysicalKey_of_reflectsTargetSubgroup
    (hreflect : ReflectsTargetSubgroup C) :
    ReflectsPhysicalKey C := by
  intro H K hblocks htarget
  apply hreflect hblocks
  have hsubgroup := congrArg (fun t : Target N C.1.1 ↦ t.2.1) htarget
  simpa only [BinaryS16DirectPhysicalTarget.target,
    BinaryS16DirectPhysicalTarget.reindexTarget_subgroup,
    targetSubgroup] using hsubgroup

/-- Concrete physical-key reflection gives the pair injection required by
the mixed physical encoder.  We state injectivity with explicit arguments so
Lean does not eagerly normalize the large dependent fixed-support subtype. -/
theorem physicalKey_injective_of_reflection
    (hreflect : ReflectsPhysicalKey C) {H K : Actual C}
    (h : physicalKey C H = physicalKey C K) : H = K := by
  change
    (blocks C H, BinaryS16DirectPhysicalTarget.target C H) =
      (blocks C K, BinaryS16DirectPhysicalTarget.target C K) at h
  have hparts := Prod.mk.inj h
  have hsource :
      BinaryS16DirectPhysicalTarget.subgroup C H =
        BinaryS16DirectPhysicalTarget.subgroup C K :=
    hreflect hparts.1 hparts.2
  exact actual_ext C hsource

/-- The final chart-varying target-subgroup theorem therefore supplies the
concrete pair injection directly. -/
theorem physicalKey_injective_of_targetSubgroup_reflection
    (hreflect : ReflectsTargetSubgroup C) {H K : Actual C}
    (h : physicalKey C H = physicalKey C K) : H = K :=
  physicalKey_injective_of_reflection C
    (reflectsPhysicalKey_of_reflectsTargetSubgroup C hreflect) h

/-- A pair-injectivity theorem immediately makes every literal mixed-table /
physical-target key fibre a subsingleton. -/
theorem keyFibre_subsingleton_of_physicalKey_injective
    (hinjective : Function.Injective (physicalKey C))
    (d : CanonicalMixedBlockTable N C.1.1)
    (t : Target N C.1.1) :
    Subsingleton
      (BinaryDegreeEightSixteenPhysicalEncoding.KeyFibre
        (blocks C) (BinaryS16DirectPhysicalTarget.target C) d t) := by
  apply keyFibre_subsingleton_of_blocks_target_injective
    (blocks C) (BinaryS16DirectPhysicalTarget.target C)
  · simpa only [physicalKey] using hinjective

/-- The concrete reflection obligation also gives the key-fibre statement
used by dependent-profile aggregation. -/
theorem keyFibre_subsingleton_of_reflection
    (hreflect : ReflectsPhysicalKey C)
    (d : CanonicalMixedBlockTable N C.1.1)
    (t : Target N C.1.1) :
    Subsingleton
      (BinaryDegreeEightSixteenPhysicalEncoding.KeyFibre
        (blocks C) (BinaryS16DirectPhysicalTarget.target C) d t) :=
  keyFibre_subsingleton_of_physicalKey_injective C
    (fun _ _ h ↦ physicalKey_injective_of_reflection C hreflect h) d t

/-- Key-fibre form of the minimal literal target-subgroup reflection
interface. -/
theorem keyFibre_subsingleton_of_targetSubgroup_reflection
    (hreflect : ReflectsTargetSubgroup C)
    (d : CanonicalMixedBlockTable N C.1.1)
    (t : Target N C.1.1) :
    Subsingleton
      (BinaryDegreeEightSixteenPhysicalEncoding.KeyFibre
        (blocks C) (BinaryS16DirectPhysicalTarget.target C) d t) :=
  keyFibre_subsingleton_of_physicalKey_injective C
    (fun _ _ h ↦ physicalKey_injective_of_targetSubgroup_reflection C hreflect h) d t

/-- Package a proved concrete pair injection as the mixed `K = 10` physical
encoding on this fixed-support fibre. -/
def physicalEncodingOfPhysicalKeyInjective {hN : 4 ≤ N}
    (hinjective : Function.Injective (physicalKey C)) :
    PhysicalEncoding (Actual C) N C.1.1 hN where
  blocks := blocks C
  target := BinaryS16DirectPhysicalTarget.target C
  joint_injective := by
    simpa only [physicalKey] using hinjective

/-- Reflection is the only mathematical input needed to construct the mixed
physical encoding on one support fibre. -/
def physicalEncodingOfReflection {hN : 4 ≤ N}
    (hreflect : ReflectsPhysicalKey C) :
    PhysicalEncoding (Actual C) N C.1.1 hN :=
  physicalEncodingOfPhysicalKeyInjective C
    (fun _ _ h ↦ physicalKey_injective_of_reflection C hreflect h)

/-- Package the minimal target-subgroup reflection theorem as the complete
mixed physical encoding. -/
def physicalEncodingOfTargetSubgroupReflection {hN : 4 ≤ N}
    (hreflect : ReflectsTargetSubgroup C) :
    PhysicalEncoding (Actual C) N C.1.1 hN :=
  physicalEncodingOfPhysicalKeyInjective C
    (fun _ _ h ↦ physicalKey_injective_of_targetSubgroup_reflection C hreflect h)

/-- Once reflection is proved uniformly in the support, the existing direct
fixed-support theorem gives the complete positive residual packed sum. -/
theorem positiveResidual_card_le_packed_sum_of_reflection
    {N : ℕ} (hN : 4 ≤ N)
    (hreflect : ∀ C : SupportIndex N, ReflectsPhysicalKey C) :
    Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) ≤
      ∑ C : SupportIndex N,
        (2 * N + 2) ^ (10 * (2 * C.1.1)) *
          ∑ b : RetainedBin N C.1.1,
            Nat.card (PhysicalFamily
              (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
  apply positiveResidual_card_le_packed_sum_of_keyFibre_subsingleton
    hN blocks BinaryS16DirectPhysicalTarget.target
  intro C d t
  exact keyFibre_subsingleton_of_reflection C (hreflect C) d t

/-- Uniform reflection of the literal physical target subgroups is already
enough for the complete positive residual packed sum. -/
theorem positiveResidual_card_le_packed_sum_of_targetSubgroup_reflection
    {N : ℕ} (hN : 4 ≤ N)
    (hreflect : ∀ C : SupportIndex N, ReflectsTargetSubgroup C) :
    Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) ≤
      ∑ C : SupportIndex N,
        (2 * N + 2) ^ (10 * (2 * C.1.1)) *
          ∑ b : RetainedBin N C.1.1,
            Nat.card (PhysicalFamily
              (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) :=
  positiveResidual_card_le_packed_sum_of_reflection hN
    (fun C ↦ reflectsPhysicalKey_of_reflectsTargetSubgroup C (hreflect C))

/-- The same uniform reflection theorem closes the residual family after the
already-owned even-critical branch is adjoined. -/
theorem residual_card_le_critical_add_packed_sum_of_reflection
    {N : ℕ} (hN : 4 ≤ N)
    (hreflect : ∀ C : SupportIndex N, ReflectsPhysicalKey C) :
    Nat.card (BinaryS16ResidualPartition.ResidualFamily N) ≤
      Nat.card (EvenCriticalSubgroups N) +
        ∑ C : SupportIndex N,
          (2 * N + 2) ^ (10 * (2 * C.1.1)) *
            ∑ b : RetainedBin N C.1.1,
              Nat.card (PhysicalFamily
                (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
  apply residual_card_le_critical_add_packed_sum_of_keyFibre_subsingleton
    hN blocks BinaryS16DirectPhysicalTarget.target
  intro C d t
  exact keyFibre_subsingleton_of_reflection C (hreflect C) d t

/-- Final residual form of the minimal literal target-subgroup reflection
interface. -/
theorem residual_card_le_critical_add_packed_sum_of_targetSubgroup_reflection
    {N : ℕ} (hN : 4 ≤ N)
    (hreflect : ∀ C : SupportIndex N, ReflectsTargetSubgroup C) :
    Nat.card (BinaryS16ResidualPartition.ResidualFamily N) ≤
      Nat.card (EvenCriticalSubgroups N) +
        ∑ C : SupportIndex N,
          (2 * N + 2) ^ (10 * (2 * C.1.1)) *
            ∑ b : RetainedBin N C.1.1,
              Nat.card (PhysicalFamily
                (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) :=
  residual_card_le_critical_add_packed_sum_of_reflection hN
    (fun C ↦ reflectsPhysicalKey_of_reflectsTargetSubgroup C (hreflect C))

end SymmetricSubgroupAsymptotics.BinaryS16DirectPhysicalEncoding

end
