import SymmetricSubgroupAsymptotics.BinaryS16CommonSourceTransport

/-!
# The final semantic boundary of the direct S16 decoder

The orbit partition and all local source actions have now been aligned.  The
only remaining carrier statement is that equality of the physical target
transports the complete correlated flat source through that canonical
alignment.  This file names exactly that statement and shows that it is
equivalent to the public target-subgroup reflection obligation.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16DirectDecoderBridge

open SymmetricSubgroupAsymptotics
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryS16CommonSourceTransport
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16JointOrbitData

variable {N : ℕ} (C : BinaryS16DirectFixedSupportClosure.SupportIndex N)

abbrev Actual := BinaryS16DirectPhysicalTarget.Actual C

/-- The exact final carrier obligation after all orbit and local-action
alignment has been discharged.  It retains every cross-orbit correlation in
the complete flat source. -/
def ReflectsCanonicalFlatSource : Prop :=
  ∀ ⦃H K : Actual C⦄,
    ∀ (hblocks : BinaryS16DirectPhysicalEncoding.blocks C H =
        BinaryS16DirectPhysicalEncoding.blocks C K)
      (htarget : targetSubgroup C H = targetSubgroup C K),
    (CanonicalOrbitWord.flatSource
        (Points (subgroup C H) (residualSector C H))
        (action (subgroup C H) (residualSector C H))
        (subgroup C H)
        (data (subgroup C H) (residualSector C H))).map
          (canonicalFlatGroupEquiv C hblocks htarget).toMonoidHom =
      CanonicalOrbitWord.flatSource
        (Points (subgroup C K) (residualSector C K))
        (action (subgroup C K) (residualSector C K))
        (subgroup C K)
        (data (subgroup C K) (residualSector C K))

/-- Reflection of the complete transported flat source closes the public
literal target-subgroup decoder. -/
theorem reflectsTargetSubgroup_of_flatSource
    (hreflect : ReflectsCanonicalFlatSource C) :
    ReflectsTargetSubgroup C := by
  intro H K hblocks htarget
  apply (canonicalFlatSource_transport_iff_subgroup_eq
    C hblocks htarget).mp
  exact hreflect hblocks htarget

/-- Conversely, the public decoder implies the flat-source statement.  Thus
the named carrier obligation loses no strength and is the exact remaining
target. -/
theorem flatSource_of_reflectsTargetSubgroup
    (hreflect : ReflectsTargetSubgroup C) :
    ReflectsCanonicalFlatSource C := by
  intro H K hblocks htarget
  apply (canonicalFlatSource_transport_iff_subgroup_eq
    C hblocks htarget).mpr
  exact hreflect hblocks htarget

theorem reflectsCanonicalFlatSource_iff :
    ReflectsCanonicalFlatSource C ↔ ReflectsTargetSubgroup C :=
  ⟨reflectsTargetSubgroup_of_flatSource C,
    flatSource_of_reflectsTargetSubgroup C⟩

end SymmetricSubgroupAsymptotics.BinaryS16DirectDecoderBridge

end
