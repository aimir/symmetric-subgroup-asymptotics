import SymmetricSubgroupAsymptotics.CFSGTwistedA2RootTransfer
import SymmetricSubgroupAsymptotics.CFSGTwistedAFixedNaturalImage
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalUnitTwist

/-! A converse to the natural fixed-image equation in actual rank two.
It uses the explicit original-lattice basis, and therefore constructs
members of the SAME original fixed subgroup from verified natural unit
words. It does not identify that subgroup with a named unitary group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
open CFSG.Models.Chevalley CFSGTwistedANaturalMatrices CFSGSerreSquareZeroMatrix

theorem originalTwistSpace_surjective (q : CFSG.PrimePower) :
    Function.Surjective (originalTwistSpace 2 q) := by
  intro y
  let e := CFSGSerreDiagram.spaceEquiv A (q.Extension 2) Fin.revPerm
    (CFSGSerreDiagram.typeA_reverse_preserves 2)
  let f := CFSGSerreField.tensorEquiv A (q.Extension 2)
    (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2)
  obtain ⟨z, rfl⟩ := e.surjective y
  obtain ⟨x, rfl⟩ := f.surjective z
  exact ⟨x, rfl⟩

theorem model_mem_fixed_iff_natural_equation (q : CFSG.PrimePower)
    (g : Model A (q.Extension 2)) :
    g.val ∈ fixedSubgroup A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order) ↔
      ∀ x : Space A (q.Extension 2),
        naturalTwistMatrix 2 q (baseChange (realizationData 2) (q.Extension 2) (g.val x)) =
          baseChange (realizationData 2) (q.Extension 2) (g.val (originalTwistSpace 2 q x)) := by
  constructor
  · intro hg x
    exact fixed_natural_image_equation 2 q ⟨g.val, hg⟩ x
  · intro hg
    have hcomm (x : Space A (q.Extension 2)) :
        originalTwistSpace 2 q (g.val x) = g.val (originalTwistSpace 2 q x) := by
      apply naturalBaseChange_injective (q.Extension 2)
      rw [naturalBaseChange_twistSpace]
      exact hg x
    have hfix : CFSGSerreOrdinaryTwists.typeAAmbientAction 2 q g.val = g.val := by
      apply LinearEquiv.ext
      intro z
      obtain ⟨x, rfl⟩ := originalTwistSpace_surjective q z
      have h := original_diagram_field_intertwines (q.Extension 2)
        (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) 2 g.val x
      change CFSGSerreOrdinaryTwists.typeAAmbientAction 2 q g.val
        (originalTwistSpace 2 q x) = originalTwistSpace 2 q (g.val x) at h
      exact h.trans (hcomm x)
    refine ⟨g.property, ?_⟩
    exact (CFSGSerreOrdinaryTwists.typeA_mem_twistGraph_iff 2 q (g.val, g.val)).mpr
      ⟨g.property, hfix.symm⟩

theorem elementaryToModel_mem_fixed_of_unit_fixed (q : CFSG.PrimePower)
    (u : NaturalElementary (q.Extension 2) 2)
    (hu : diagramFieldUnitHom (q.Extension 2) 2
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom u.val = u.val) :
    (elementaryToModel (q.Extension 2) u).val ∈
      fixedSubgroup A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order) := by
  let K := q.Extension 2
  let g := elementaryToModel K u
  have hinter (x : Space A K) :
      baseChange (realizationData 2) K (g.val x) =
        (u.val : Mat K 2) * baseChange (realizationData 2) K x *
          (↑(u.val⁻¹) : Mat K 2) := by
    have he := congrArg (fun f : NaturalImage K 2 ≃ₗ[K] NaturalImage K 2 =>
      (f ((baseChange (realizationData 2) K).rangeRestrict x)).val)
        (elementaryToModel_action K u)
    change (imageRepresentation (realizationData 2) K g
      ((baseChange (realizationData 2) K).rangeRestrict x)).val = _ at he
    simpa only [imageRepresentation_intertwines] using he
  apply (model_mem_fixed_iff_natural_equation q g).mpr
  intro x
  rw [hinter]
  change matrixDiagram K 2
      ((CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom.mapMatrix
        ((u.val : Mat K 2) * baseChange (realizationData 2) K x *
          (↑(u.val⁻¹) : Mat K 2))) = _
  rw [diagramField_conjugation, hu]
  change (u.val : Mat K 2) *
    naturalTwistMatrix 2 q (baseChange (realizationData 2) K x) *
      (↑(u.val⁻¹) : Mat K 2) = _
  rw [← naturalBaseChange_twistSpace]
  exact (hinter (originalTwistSpace 2 q x)).symm

def fixedElementOfNaturalUnit (q : CFSG.PrimePower)
    (u : NaturalElementary (q.Extension 2) 2)
    (hu : diagramFieldUnitHom (q.Extension 2) 2
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom u.val = u.val) :
    fixedSubgroup A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order) :=
  ⟨(elementaryToModel (q.Extension 2) u).val,
    elementaryToModel_mem_fixed_of_unit_fixed q u hu⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
