import SymmetricSubgroupAsymptotics.CFSGTwistedAFixedSimilitudeLift

/-! The literal pullback of the original fixed action and the natural
elementary action. Its source projection is surjective by the proved
action-range equality. Every natural coordinate of this actual pullback
is a signed-form similitude. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley

abbrev OriginalFixedA (r : ℕ) (q : CFSG.PrimePower) :=
  fixedSubgroup (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)

def fixedNaturalPullback (r : ℕ) (q : CFSG.PrimePower) :
    Subgroup (OriginalFixedA r q × NaturalElementary (q.Extension 2) r) :=
  ((twistedFixedAction r q).comp
    (MonoidHom.fst (OriginalFixedA r q) (NaturalElementary (q.Extension 2) r))).eqLocus
      ((naturalElementaryAction (q.Extension 2) r).comp
        (MonoidHom.snd (OriginalFixedA r q) (NaturalElementary (q.Extension 2) r)))

def pullbackSource (r : ℕ) (q : CFSG.PrimePower) :
    fixedNaturalPullback r q →* OriginalFixedA r q :=
  (MonoidHom.fst _ _).comp (fixedNaturalPullback r q).subtype

def pullbackElementary (r : ℕ) (q : CFSG.PrimePower) :
    fixedNaturalPullback r q →* NaturalElementary (q.Extension 2) r :=
  (MonoidHom.snd _ _).comp (fixedNaturalPullback r q).subtype

def pullbackMatrix (r : ℕ) (q : CFSG.PrimePower) :
    fixedNaturalPullback r q →* (Mat (q.Extension 2) r)ˣ :=
  (NaturalElementary (q.Extension 2) r).subtype.comp (pullbackElementary r q)

theorem pullback_action_eq (r : ℕ) (q : CFSG.PrimePower)
    (p : fixedNaturalPullback r q) :
    naturalElementaryAction (q.Extension 2) r (pullbackElementary r q p) =
      twistedFixedAction r q (pullbackSource r q p) := p.property.symm

theorem pullbackSource_surjective (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower) :
    Function.Surjective (pullbackSource r q) := by
  intro g
  obtain ⟨u, hu, _⟩ := fixed_natural_similitude_lift r hr q g
  exact ⟨⟨(g, u), hu.symm⟩, rfl⟩

theorem pullbackMatrix_similitude (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    (p : fixedNaturalPullback r q) :
    ∃ c : q.Extension 2, c ≠ 0 ∧
      ((CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom.mapMatrix
        (pullbackMatrix r q p : Mat (q.Extension 2) r)).transpose *
        (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r) *
          (pullbackMatrix r q p : Mat (q.Extension 2) r) =
            c • (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r) := by
  let g := pullbackSource r q p
  let u := pullbackElementary r q p
  let gM := CFSGSerreFixedRootElements.fixedToModel (CartanMatrix.A r) (q.Extension 2)
    CFSG.Models.reverseNode (fun _ => q.order) g
  have hu : naturalElementaryAction (q.Extension 2) r u = naturalAction (q.Extension 2) r gM :=
    pullback_action_eq r q p
  have hinter (x : Space (CartanMatrix.A r) (q.Extension 2)) :
      (u.val : Mat (q.Extension 2) r) *
        CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2) x *
          (↑(u.val⁻¹) : Mat (q.Extension 2) r) =
        CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2) (g.val x) := by
    calc
      _ = (naturalElementaryAction (q.Extension 2) r u
          ((CFSGSerreSquareZeroMatrix.baseChange (realizationData r)
            (q.Extension 2)).rangeRestrict x)).val := rfl
      _ = (naturalAction (q.Extension 2) r gM
          ((CFSGSerreSquareZeroMatrix.baseChange (realizationData r)
            (q.Extension 2)).rangeRestrict x)).val :=
        congrArg Subtype.val (DFunLike.congr_fun hu _)
      _ = _ := CFSGSerreSquareZeroMatrix.imageRepresentation_intertwines
        (realizationData r) (q.Extension 2) gM x
  apply natural_twist_equivariant_lift_similitude (q.Extension 2) r hr
    (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom u.val
  intro x
  change naturalTwistMatrix r q
      ((u.val : Mat (q.Extension 2) r) *
        CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2) x *
          (↑(u.val⁻¹) : Mat (q.Extension 2) r)) =
    (u.val : Mat (q.Extension 2) r) *
      naturalTwistMatrix r q
        (CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2) x) *
          (↑(u.val⁻¹) : Mat (q.Extension 2) r)
  rw [hinter, fixed_natural_image_equation, ← naturalBaseChange_twistSpace]
  exact (hinter (originalTwistSpace r q x)).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
