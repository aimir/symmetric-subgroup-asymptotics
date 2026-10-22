import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalNaturalFaithfulness
import SymmetricSubgroupAsymptotics.CFSGTwistedAFixedNaturalImage
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalUnitTwist

/-! Exact natural/source fixed correspondence in every rank. The
proved original integral tensor basis permits the converse fixed-image
equation and lifts verified natural fixed unit words to the SAME original
fixed subgroup, without simplicity or a supplied SU identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
open CFSG.Models.Chevalley CFSGTwistedANaturalMatrices CFSGSerreSquareZeroMatrix
variable (r : ℕ)

theorem originalTwistSpace_surjective (q : CFSG.PrimePower) :
    Function.Surjective (originalTwistSpace r q) := by
  intro y
  let e := CFSGSerreDiagram.spaceEquiv (CartanMatrix.A r) (q.Extension 2) Fin.revPerm
    (CFSGSerreDiagram.typeA_reverse_preserves r)
  let f := CFSGSerreField.tensorEquiv (CartanMatrix.A r) (q.Extension 2)
    (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2)
  obtain ⟨z, rfl⟩ := e.surjective y
  obtain ⟨x, rfl⟩ := f.surjective z
  exact ⟨x, rfl⟩

theorem model_mem_fixed_iff_natural_equation (q : CFSG.PrimePower)
    (g : Model (CartanMatrix.A r) (q.Extension 2)) :
    g.val ∈ fixedSubgroup (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order) ↔
      ∀ x : Space (CartanMatrix.A r) (q.Extension 2),
        naturalTwistMatrix r q (baseChange (realizationData r) (q.Extension 2) (g.val x)) =
          baseChange (realizationData r) (q.Extension 2) (g.val (originalTwistSpace r q x)) := by
  constructor
  · intro hg x
    exact fixed_natural_image_equation r q ⟨g.val, hg⟩ x
  · intro hg
    have hcomm (x : Space (CartanMatrix.A r) (q.Extension 2)) :
        originalTwistSpace r q (g.val x) = g.val (originalTwistSpace r q x) := by
      apply naturalBaseChange_injective (q.Extension 2) r
      rw [naturalBaseChange_twistSpace]
      exact hg x
    have hfix : CFSGSerreOrdinaryTwists.typeAAmbientAction r q g.val = g.val := by
      apply LinearEquiv.ext
      intro z
      obtain ⟨x, rfl⟩ := originalTwistSpace_surjective r q z
      have h := original_diagram_field_intertwines (q.Extension 2)
        (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) r g.val x
      change CFSGSerreOrdinaryTwists.typeAAmbientAction r q g.val
        (originalTwistSpace r q x) = originalTwistSpace r q (g.val x) at h
      exact h.trans (hcomm x)
    refine ⟨g.property, ?_⟩
    exact (CFSGSerreOrdinaryTwists.typeA_mem_twistGraph_iff r q (g.val, g.val)).mpr
      ⟨g.property, hfix.symm⟩

theorem elementaryToModel_mem_fixed_of_unit_fixed (q : CFSG.PrimePower)
    (u : NaturalElementary (q.Extension 2) r)
    (hu : diagramFieldUnitHom (q.Extension 2) r
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom u.val = u.val) :
    (elementaryToModel (q.Extension 2) r u).val ∈
      fixedSubgroup (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order) := by
  let K := q.Extension 2
  let g := elementaryToModel K r u
  have hinter (x : Space (CartanMatrix.A r) K) :
      baseChange (realizationData r) K (g.val x) =
        (u.val : Mat K r) * baseChange (realizationData r) K x *
          (↑(u.val⁻¹) : Mat K r) := by
    have he := congrArg (fun f : NaturalImage K r ≃ₗ[K] NaturalImage K r =>
      (f ((baseChange (realizationData r) K).rangeRestrict x)).val)
        (elementaryToModel_action K r u)
    change (imageRepresentation (realizationData r) K g
      ((baseChange (realizationData r) K).rangeRestrict x)).val = _ at he
    simpa only [imageRepresentation_intertwines] using he
  apply (model_mem_fixed_iff_natural_equation r q g).mpr
  intro x
  rw [hinter]
  change matrixDiagram K r
      ((CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom.mapMatrix
        ((u.val : Mat K r) * baseChange (realizationData r) K x *
          (↑(u.val⁻¹) : Mat K r))) = _
  rw [diagramField_conjugation, hu]
  change (u.val : Mat K r) *
    naturalTwistMatrix r q (baseChange (realizationData r) K x) *
      (↑(u.val⁻¹) : Mat K r) = _
  rw [← naturalBaseChange_twistSpace]
  exact (hinter (originalTwistSpace r q x)).symm

def fixedElementOfNaturalUnit (q : CFSG.PrimePower)
    (u : NaturalElementary (q.Extension 2) r)
    (hu : diagramFieldUnitHom (q.Extension 2) r
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom u.val = u.val) :
    fixedSubgroup (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order) :=
  ⟨(elementaryToModel (q.Extension 2) r u).val,
    elementaryToModel_mem_fixed_of_unit_fixed r q u hu⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
