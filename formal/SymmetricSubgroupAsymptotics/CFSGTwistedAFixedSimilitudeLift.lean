import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalSimilitude
import SymmetricSubgroupAsymptotics.CFSGTwistedAFixedNaturalImage

/-! Every element of the ORIGINAL fixed Serre group has an actual
elementary natural lift which is a similitude of the signed form. Only
the action on the original integral tensor image is lifted. Equality of
the source with a unitary matrix group is not asserted. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley

theorem fixed_natural_similitude_lift (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    (g : fixedSubgroup (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode
      (fun _ => q.order)) :
    ∃ u : NaturalElementary (q.Extension 2) r,
      naturalElementaryAction (q.Extension 2) r u = twistedFixedAction r q g ∧
        ∃ c : q.Extension 2, c ≠ 0 ∧
          ((CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom.mapMatrix
            (u.val : Mat (q.Extension 2) r)).transpose *
            (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r) *
              (u.val : Mat (q.Extension 2) r) =
                c • (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r) := by
  let gM := CFSGSerreFixedRootElements.fixedToModel (CartanMatrix.A r) (q.Extension 2)
    CFSG.Models.reverseNode (fun _ => q.order) g
  have hmem : naturalAction (q.Extension 2) r gM ∈
      (naturalElementaryAction (q.Extension 2) r).range := by
    rw [← naturalAction_ranges_eq]
    exact ⟨gM, rfl⟩
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, hu, ?_⟩
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
