import SymmetricSubgroupAsymptotics.TransitivePairingCount
import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance

/-!
# Distinct original pairings realized by binary frames

The counted datum is the partner function on the original points, not a
choice of pair labels or orientations. Each realized partner function has
one auxiliary frame chosen once. The choice is not additional counted data.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace BinaryPairFrame

variable {X I : Type*} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

/-- Swap the two original points of the same frame fibre. -/
def partnerMap (x : X) : X :=
  F.frame ((F.frame.symm x).1, (F.frame.symm x).2 + 1)

@[simp] theorem partnerMap_frame (i : I) (b : ZMod 2) :
    F.partnerMap (F.frame (i,b)) = F.frame (i,b+1) := by
  simp only [partnerMap, Equiv.symm_apply_apply]

theorem partnerMap_involutive : Function.Involutive F.partnerMap := by
  intro x
  obtain ⟨⟨i,b⟩,rfl⟩ := F.frame.surjective x
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide +kernel
  simp only [partnerMap_frame, add_assoc, htwo, add_zero]

theorem partnerMap_ne (x : X) : F.partnerMap x ≠ x := by
  obtain ⟨⟨i,b⟩,rfl⟩ := F.frame.surjective x
  intro h
  rw [F.partnerMap_frame] at h
  have hb : b+1=b := congrArg Prod.snd (F.frame.injective h)
  have hcancel : b+1=b+0 := hb.trans (add_zero b).symm
  exact one_ne_zero (add_left_cancel hcancel)

/-- The offsets of the actual original action commute with the bit swap.
No enlarged flip group or replacement top action is used. -/
theorem partnerMap_equivariant (u : U) (x : X) :
    F.partnerMap (u • x) = u • F.partnerMap x := by
  obtain ⟨⟨i,b⟩,rfl⟩ := F.frame.surjective x
  change F.partnerMap ((u : Equiv.Perm X) (F.frame (i,b))) =
    (u : Equiv.Perm X) (F.partnerMap (F.frame (i,b)))
  simp only [partnerMap_frame, action_frame]
  apply congrArg F.frame
  exact congrArg (fun z : ZMod 2 => ((F.top u) i, z))
    (add_right_comm b (F.offset u i) 1)

/-- The actual partner function associated with a labelled frame. -/
def underlyingPairing : EquivariantPairing U X :=
  ⟨F.partnerMap, F.partnerMap_involutive, F.partnerMap_ne,
    F.partnerMap_equivariant⟩

end BinaryPairFrame

/-- Distinct original pairings admitting a frame with this index type.
The realizing frame occurs only in an existential proposition. -/
def RealizedPairing {X : Type*} (U : Subgroup (Equiv.Perm X)) (I : Type*) :=
  {p : EquivariantPairing U X // ∃ F : BinaryPairFrame U I,
    F.underlyingPairing = p}

namespace BinaryPairFrame

variable {X I : Type*} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

/-- Every actual frame contributes its original pairing to the same
realized family, even when many labelled frames give that pairing. -/
def realizedPairing : RealizedPairing U I :=
  ⟨F.underlyingPairing, F, rfl⟩

@[simp] theorem realizedPairing_val :
    F.realizedPairing.1 = F.underlyingPairing := rfl

end BinaryPairFrame

namespace RealizedPairing

variable {X I : Type*} {U : Subgroup (Equiv.Perm X)}

/-- One auxiliary original frame per distinct realized pairing. -/
def chosenFrame (p : RealizedPairing U I) : BinaryPairFrame U I :=
  p.2.choose

@[simp] theorem chosenFrame_underlyingPairing (p : RealizedPairing U I) :
    p.chosenFrame.underlyingPairing = p.1 :=
  p.2.choose_spec

/-- Choosing and then forgetting the auxiliary frame recovers the SAME
original pairing, not merely an isomorphic pair system. -/
@[simp] theorem chosenFrame_realizedPairing (p : RealizedPairing U I) :
    p.chosenFrame.realizedPairing = p :=
  Subtype.ext p.chosenFrame_underlyingPairing

theorem finite [Finite X] : Finite (RealizedPairing U I) := by
  unfold RealizedPairing EquivariantPairing
  infer_instance

/-- Only distinct original partner functions are counted. The index type
can be arbitrary; no cardinality bound on all labelled frames is claimed. -/
theorem card_le [Finite X] [MulAction.IsPretransitive U X] (x : X) :
    Nat.card (RealizedPairing U I) ≤ Nat.card X - 1 := by
  letI : Finite (EquivariantPairing U X) := by
    unfold EquivariantPairing
    infer_instance
  have h := Nat.card_le_card_of_injective
    (fun p : RealizedPairing U I => p.1) Subtype.val_injective
  exact h.trans (EquivariantPairing.card_le (G := U) x)

theorem card_le_of_nonempty [Finite X] [Nonempty X]
    [MulAction.IsPretransitive U X] :
    Nat.card (RealizedPairing U I) ≤ Nat.card X - 1 :=
  card_le (Classical.choice (inferInstance : Nonempty X))

end RealizedPairing
end SymmetricSubgroupAsymptotics

end
