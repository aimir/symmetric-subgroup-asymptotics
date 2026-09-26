import SymmetricSubgroupAsymptotics.BinaryCarrierMasterEnvelopes

/-! Fourteen scalar envelope labels for the five original degree-sixteen
masters: the twelve displayed H16 rows and two proved star envelopes.
Every label has physical scale two. Labels are not normal subgroups, and
their number does not bound the number or total weight of original axes. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMasterMenu

abbrev Label := Fin 14

def h16Label (i : Fin 12) : Label := ⟨i.val, by omega⟩

def starCrossingLabel : Label := 12
def starIntermediateLabel : Label := 13

def envelope (i : Label) : JointCapacityRow :=
  if hi : i.val < 12 then BinaryCarrierMasterEnvelopes.h16 ⟨i.val, hi⟩ else
  if i.val = 12 then BinaryCarrierStarEnvelope.coarseEnvelope else
  ⟨3,5,3,1,4,1⟩

/-- This is the common degree-sixteen scale convention, not a weight
assigned to a normal subgroup and not a sum over distinct row labels. -/
def physicalScale (_ : Label) : ℝ := 2

@[simp] theorem envelope_h16 (i : Fin 12) :
    envelope (h16Label i) = BinaryCarrierMasterEnvelopes.h16 i := by
  simp [envelope, h16Label, i.isLt]

@[simp] theorem envelope_starCrossing :
    envelope starCrossingLabel = BinaryCarrierStarEnvelope.coarseEnvelope := rfl

@[simp] theorem envelope_starIntermediate :
    envelope starIntermediateLabel = ⟨3,5,3,1,4,1⟩ := rfl

@[simp] theorem physicalScale_eq (i : Label) : physicalScale i = 2 := rfl

end SymmetricSubgroupAsymptotics.BinaryCarrierMasterMenu
