import SymmetricSubgroupAsymptotics.BinaryDegree16PhysicalAnalyticClosure
import SymmetricSubgroupAsymptotics.BinaryOriginalWeightedDirectEntry
import SymmetricSubgroupAsymptotics.BinarySevenCharacterInstalled
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport

/-!
# Direct routing for the completed degree-sixteen frontier

The degree-sixteen structural closure has three direct constructors.  The
intrinsic constructor contains either the common accepted-entry structure or
the installed order/seven-character certificate; the two catalogue
constructors contain an accepted entry after one literal point conjugation.

This file gives all three branches one interface.  It retains the point
conjugation, the transported original normal, and the complete exterior
model.  No quotient is replaced by an isomorphic abstract target and no
exterior correlation is discarded.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegree16DirectOwnerRouting

open SymmetricSubgroupAsymptotics
open BinaryDegree16SplitFrontier
open BinaryDegree16SplitAnalyticClosure
open BinaryDegree16PhysicalAnalyticClosure

variable {U : Subgroup (Equiv.Perm (Fin 16))}
    {N : Subgroup U} [N.Normal]

/-- The installed order/seven-character certificate has exactly the common
accepted-entry fields.  The binary permutation class theorem is discharged
internally, so the resulting entry has no remaining class-count premise. -/
def orderSevenAcceptedEntry (hU : IsPGroup 2 U)
    (C : BinaryOrderSevenCharacterCertificate U N) : AcceptedEntry U N where
  prefixDegree := C.prefixDegree
  markerHalf := C.markerHalf
  liftConstant := C.liftConstant
  gapParameter := C.gapParameter
  momentWeight := fun {b} J => C.momentWeight J
  prefix_eq_two_mul := C.prefixDegree_eq_two_mul
  prefix_lt := C.prefixDegree_lt (show 0 < 16 by decide)
  liftConstant_nonneg := C.liftConstant_nonneg
  gapParameter_pos := C.gapParameter_pos
  moment_le := C.moment_le
  original_envelope := fun {b} P J =>
    BinaryOrderSevenCharacterCertificate.original_envelope C
      (h := 8) BinarySevenCharacterInstalled.class_input hU P J

/-- Both intrinsic accepted alternatives reduce to one actual entry on the
unchanged action and literal original normal. -/
theorem acceptedAxis_entry (hU : IsPGroup 2 U) (O : AcceptedAxis U N) :
    Nonempty (AcceptedEntry U N) := by
  rcases O with hentry | horder
  · exact hentry
  · obtain ⟨C⟩ := horder
    exact ⟨orderSevenAcceptedEntry hU C⟩

/-- Pull an accepted catalogue entry back to the literal original action.
The numerical parameters and moment weight are unchanged.  For the local
envelope we enlarge the surviving subtype to all epimorphisms, transport
that complete finite set through the conjugate quotient, and invoke the
catalogue entry with the unrestricted survival predicate.  Thus the later
physical sum uses the original action normalizer. -/
def pullbackConjugateAcceptedEntry
    {V : Subgroup (Equiv.Perm (Fin 16))}
    (g : Equiv.Perm (Fin 16)) (hg : MulAut.conj g • U = V)
    (E : AcceptedEntry V (actionConjugacyNormal g hg N)) :
    AcceptedEntry U N where
  prefixDegree := E.prefixDegree
  markerHalf := E.markerHalf
  liftConstant := E.liftConstant
  gapParameter := E.gapParameter
  momentWeight := fun {b} J => E.momentWeight J
  prefix_eq_two_mul := E.prefix_eq_two_mul
  prefix_lt := E.prefix_lt
  liftConstant_nonneg := E.liftConstant_nonneg
  gapParameter_pos := E.gapParameter_pos
  moment_le := E.moment_le
  original_envelope := by
    intro b P J
    have hsubNat :
        Nat.card {β : GroupEpimorphism J (U ⧸ N) //
          P (fusionFullGoursatEncode ⟨N,inferInstance⟩ J β).1} ≤
          Nat.card (GroupEpimorphism J (U ⧸ N)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hquot :
        Nat.card (GroupEpimorphism J (U ⧸ N)) =
          Nat.card (GroupEpimorphism J
            (V ⧸ actionConjugacyNormal g hg N)) :=
      fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
        (actionConjugacyQuotient g hg N)
    calc
      fusionSurvivingEpiCount U P ⟨N,inferInstance⟩ J ≤
          (Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ) := by
        unfold fusionSurvivingEpiCount
        exact_mod_cast hsubNat
      _ = (Nat.card (GroupEpimorphism J
          (V ⧸ actionConjugacyNormal g hg N)) : ℝ) := by
        exact_mod_cast hquot
      _ ≤ fusionLocalFactor b 8 E.prefixDegree E.liftConstant E.gapParameter *
          E.momentWeight J := by
        let e : {β : GroupEpimorphism J
            (V ⧸ actionConjugacyNormal g hg N) // True} ≃
            GroupEpimorphism J (V ⧸ actionConjugacyNormal g hg N) :=
          { toFun := Subtype.val
            invFun := fun β => ⟨β,trivial⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        have he := Nat.card_congr e
        have htarget := E.original_envelope (fun _ => True) J
        unfold fusionSurvivingEpiCount at htarget
        change (Nat.card {β : GroupEpimorphism J
          (V ⧸ actionConjugacyNormal g hg N) // True} : ℝ) ≤ _ at htarget
        rw [he] at htarget
        exact htarget

/-- Forget the degree-sixteen-specific name of the common direct interface. -/
def acceptedEntry_weighted (E : AcceptedEntry U N) :
    BinaryOriginalWeightedDirectEntry (h := 8) U N where
  prefixDegree := E.prefixDegree
  markerHalf := E.markerHalf
  liftConstant := E.liftConstant
  gapParameter := E.gapParameter
  momentWeight := fun {b} J => E.momentWeight J
  prefix_eq_two_mul := E.prefix_eq_two_mul
  prefix_lt := E.prefix_lt
  liftConstant_nonneg := E.liftConstant_nonneg
  gapParameter_pos := E.gapParameter_pos
  moment_le := E.moment_le
  original_envelope := E.original_envelope

/-- A direct entry together with the literal point conjugation which places
its action in the entry's coordinates.  `axis_eq` records that the entry is
on the transported original normal, rather than on an independently chosen
isomorphic subgroup. -/
inductive RoutedEntry
    (U : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup U) [N.Normal] : Type
  | literal (entry : AcceptedEntry U N)
  | conjugate {V : Subgroup (Equiv.Perm (Fin 16))}
      (g : Equiv.Perm (Fin 16)) (hg : MulAut.conj g • U = V)
      (entry : AcceptedEntry V (actionConjugacyNormal g hg N))

namespace RoutedEntry

variable {U : Subgroup (Equiv.Perm (Fin 16))}
    {N : Subgroup U} [N.Normal]

/-- The action on which the accepted entry is written. -/
def target (R : RoutedEntry U N) : Subgroup (Equiv.Perm (Fin 16)) :=
  match R with
  | .literal _ => U
  | @conjugate _ _ _ V _ _ _ => V

/-- The literal normal used by the routed entry. -/
def axis (R : RoutedEntry U N) : Subgroup R.target :=
  match R with
  | .literal _ => N
  | @conjugate _ _ _ _ g hg _ => actionConjugacyNormal g hg N

instance axis_normal (R : RoutedEntry U N) : R.axis.Normal := by
  cases R with
  | literal E =>
      change N.Normal
      exact inferInstance
  | @conjugate V g hg E =>
      change (actionConjugacyNormal g hg N).Normal
      exact inferInstance

/-- Recover the common numerical entry after routing. -/
def acceptedEntry (R : RoutedEntry U N) : AcceptedEntry R.target R.axis :=
  match R with
  | .literal E => E
  | .conjugate _ _ E => E

end RoutedEntry

namespace DirectOwner

variable {U : Subgroup (Equiv.Perm (Fin 16))}
    {N : Subgroup U} [N.Normal]

/-- Every direct owner reaches one uniform accepted entry, retaining the
actual conjugation used by the finite catalogue when one is present. -/
theorem routedEntry (hU : IsPGroup 2 U) (O : DirectOwner U N) :
    Nonempty (RoutedEntry U N) := by
  rcases O with haccepted | ⟨g,hg,hentry⟩ | ⟨g,hg,hentry⟩
  · obtain ⟨E⟩ := acceptedAxis_entry hU haccepted
    exact ⟨.literal E⟩
  · obtain ⟨E⟩ := hentry
    exact ⟨.conjugate g hg E⟩
  · obtain ⟨E⟩ := hentry
    exact ⟨.conjugate g hg E⟩

/-- Counting form on the unchanged original action.  Catalogue conjugacy is
used only to prove the envelope and disappears from the continuation index. -/
theorem acceptedEntry (hU : IsPGroup 2 U) (O : DirectOwner U N) :
    Nonempty (AcceptedEntry U N) := by
  rcases O with haccepted | ⟨g,hg,hentry⟩ | ⟨g,hg,hentry⟩
  · exact acceptedAxis_entry hU haccepted
  · obtain ⟨E⟩ := hentry
    exact ⟨pullbackConjugateAcceptedEntry g hg E⟩
  · obtain ⟨E⟩ := hentry
    exact ⟨pullbackConjugateAcceptedEntry g hg E⟩

/-- Every direct owner now inhabits the width-uniform recurrence interface
on the literal original action and normal. -/
theorem weightedEntry (hU : IsPGroup 2 U) (O : DirectOwner U N) :
    Nonempty (BinaryOriginalWeightedDirectEntry (h := 8) U N) := by
  obtain ⟨E⟩ := acceptedEntry hU O
  exact ⟨acceptedEntry_weighted E⟩

end DirectOwner

namespace OrbitWitness

variable {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (W : BinaryDegree16PhysicalAnalyticClosure.OrbitWitness H)

local instance witnessAxisNormal : W.axis.Normal := W.axis_normal

/-- The complete exterior model written in the coordinates of a routed
direct entry. -/
def routedModel (R : RoutedEntry W.action W.axis) :
    Subgroup (R.target × Equiv.Perm (Fin (n-16))) := by
  cases R with
  | literal => exact W.model
  | conjugate g hg _ => exact W.conjugatedModel g hg

theorem routedModel_full (R : RoutedEntry W.action W.axis) :
    (routedModel W R).map
      (MonoidHom.fst R.target (Equiv.Perm (Fin (n-16)))) = ⊤ := by
  cases R with
  | literal => exact W.model_full
  | conjugate g hg _ => exact W.conjugatedModel_full g hg

/-- The Goursat axis of the complete routed model is the exact normal used
by the accepted entry. -/
theorem routedModel_axis (R : RoutedEntry W.action W.axis) :
    (routedModel W R).goursatFst = R.axis := by
  cases R with
  | literal => rfl
  | conjugate g hg _ => exact W.conjugatedModel_axis g hg

/-- Relabelling only the selected orbit leaves the full exterior image
unchanged. -/
theorem routedModel_exterior (R : RoutedEntry W.action W.axis) :
    (routedModel W R).map
        (MonoidHom.snd R.target (Equiv.Perm (Fin (n-16)))) =
      W.model.map
        (MonoidHom.snd W.action (Equiv.Perm (Fin (n-16)))) := by
  cases R with
  | literal => rfl
  | conjugate g hg _ => exact W.conjugatedModel_exterior g hg

/-- The physical axis reaches either one routed direct entry or one exact
positive-support carrier slot, on the same complete original model. -/
theorem routedEntry_or_supported_slot :
    Nonempty (RoutedEntry W.action W.axis) ∨
      Nonempty {S : BinaryDegreeEightPhysicalAnalyticClosure.AxisSlot
        W.action W.axis // S.HasNoncritical} := by
  rcases W.direct_or_supported_slot with hdirect | hslot
  · exact Or.inl
      (SymmetricSubgroupAsymptotics.BinaryDegree16DirectOwnerRouting.DirectOwner.routedEntry
        W.action_binary hdirect)
  · exact Or.inr hslot

/-- Final local counting interface: direct owners are now entries on the
literal original action, while the residual branch remains an exact
positive-support carrier slot on that same action. -/
theorem acceptedEntry_or_supported_slot :
    Nonempty (AcceptedEntry W.action W.axis) ∨
      Nonempty {S : BinaryDegreeEightPhysicalAnalyticClosure.AxisSlot
        W.action W.axis // S.HasNoncritical} := by
  rcases W.direct_or_supported_slot with hdirect | hslot
  · exact Or.inl
      (SymmetricSubgroupAsymptotics.BinaryDegree16DirectOwnerRouting.DirectOwner.acceptedEntry
        W.action_binary hdirect)
  · exact Or.inr hslot

theorem weightedEntry_or_supported_slot :
    Nonempty (@BinaryOriginalWeightedDirectEntry 8 W.action W.axis W.axis_normal) ∨
      Nonempty {S : BinaryDegreeEightPhysicalAnalyticClosure.AxisSlot
        W.action W.axis // S.HasNoncritical} := by
  rcases W.direct_or_supported_slot with hdirect | hslot
  · exact Or.inl
      (SymmetricSubgroupAsymptotics.BinaryDegree16DirectOwnerRouting.DirectOwner.weightedEntry
        W.action_binary hdirect)
  · exact Or.inr hslot

end OrbitWitness

end SymmetricSubgroupAsymptotics.BinaryDegree16DirectOwnerRouting

end
