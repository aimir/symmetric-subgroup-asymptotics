import SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits

/-! Trace-skew highest and opposite root parameters give verified fixed
units, then actual elements of the ORIGINAL generated fixed subgroup.
These adjacent-node words are not covered by Cartan-zero pair tricks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
open CFSGTwistedANaturalMatrices CFSGTwistedA2OriginalRelations
variable (K : Type) [Field K]

theorem diagramField_highest_entry (σ : K ≃+* K) (a : K) :
    diagramFieldUnitHom K 2 σ.toRingHom
      (entryUnit K (show (0 : Fin 3) ≠ 2 by decide) a) =
        entryUnit K (show (0 : Fin 3) ≠ 2 by decide) (-σ a) := by
  let J := signedReversalUnit K 2
  have hc := CFSGOrthogonalDGenerationMonomialAction.conjugation_single
    J Fin.revPerm (signWeight K 2) (signedReversalUnit_monomial K 2)
    (2 : Fin 3) 0 (-σ a) (signWeight_ne_zero K 2 _)
  norm_num [Fin.revPerm_symm, Fin.revPerm_apply, Fin.rev, signWeight] at hc
  apply Units.ext
  rw [diagramFieldUnitHom_val, entryUnit_inv_val, entryUnit_val]
  simp only [map_add, map_one, Matrix.transpose_add, Matrix.transpose_one]
  have hs : σ.toRingHom.mapMatrix (Matrix.single (0 : Fin 3) 2 (-a)) =
      Matrix.single 0 2 (-σ a) := by
    change (Matrix.single (0 : Fin 3) 2 (-a)).map σ.toRingHom = _
    simp only [Matrix.map_single, map_neg]
    rfl
  rw [hs, Matrix.transpose_single]
  change (J : Mat K 2) * (1 + Matrix.single 2 0 (-σ a)) *
    (↑(J⁻¹) : Mat K 2) = 1 + Matrix.single 0 2 (-σ a)
  have hc' : (J : Mat K 2) * Matrix.single 2 0 (-σ a) *
      (↑(J⁻¹) : Mat K 2) = Matrix.single 0 2 (-σ a) := by
    simpa only [Matrix.coe_units_inv] using hc
  rw [mul_add, add_mul, mul_one, Units.mul_inv]
  exact congrArg (fun M : Mat K 2 => 1 + M) hc' 

theorem diagramField_opposite_entry (σ : K ≃+* K) (a : K) :
    diagramFieldUnitHom K 2 σ.toRingHom
      (entryUnit K (show (2 : Fin 3) ≠ 0 by decide) a) =
        entryUnit K (show (2 : Fin 3) ≠ 0 by decide) (-σ a) := by
  let J := signedReversalUnit K 2
  have hc := CFSGOrthogonalDGenerationMonomialAction.conjugation_single
    J Fin.revPerm (signWeight K 2) (signedReversalUnit_monomial K 2)
    (0 : Fin 3) 2 (-σ a) (signWeight_ne_zero K 2 _)
  norm_num [Fin.revPerm_symm, Fin.revPerm_apply, Fin.rev, signWeight] at hc
  apply Units.ext
  rw [diagramFieldUnitHom_val, entryUnit_inv_val, entryUnit_val]
  simp only [map_add, map_one, Matrix.transpose_add, Matrix.transpose_one]
  have hs : σ.toRingHom.mapMatrix (Matrix.single (2 : Fin 3) 0 (-a)) =
      Matrix.single 2 0 (-σ a) := by
    change (Matrix.single (2 : Fin 3) 0 (-a)).map σ.toRingHom = _
    simp only [Matrix.map_single, map_neg]
    rfl
  rw [hs, Matrix.transpose_single]
  change (J : Mat K 2) * (1 + Matrix.single 0 2 (-σ a)) *
    (↑(J⁻¹) : Mat K 2) = 1 + Matrix.single 2 0 (-σ a)
  have hc' : (J : Mat K 2) * Matrix.single 0 2 (-σ a) *
      (↑(J⁻¹) : Mat K 2) = Matrix.single 2 0 (-σ a) := by
    simpa only [Matrix.coe_units_inv] using hc
  rw [mul_add, add_mul, mul_one, Units.mul_inv]
  exact congrArg (fun M : Mat K 2 => 1 + M) hc' 

theorem highest_unit_fixed (q : CFSG.PrimePower) (a : q.Extension 2)
    (ha : a ^ q.order = -a) :
    diagramFieldUnitHom (q.Extension 2) 2
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom
        (highest (q.Extension 2) a).val = (highest (q.Extension 2) a).val := by
  rw [highest_val, diagramField_highest_entry]
  change entryUnit (q.Extension 2) _ (-(a ^ q.order)) = entryUnit (q.Extension 2) _ a
  rw [ha, neg_neg]

theorem opposite_unit_fixed (q : CFSG.PrimePower) (a : q.Extension 2)
    (ha : a ^ q.order = -a) :
    diagramFieldUnitHom (q.Extension 2) 2
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom
        (opposite (q.Extension 2) a).val = (opposite (q.Extension 2) a).val := by
  rw [opposite_val, diagramField_opposite_entry]
  change entryUnit (q.Extension 2) _ (-(a ^ q.order)) = entryUnit (q.Extension 2) _ a
  rw [ha, neg_neg]

def highestFixed (q : CFSG.PrimePower) (a : q.Extension 2) (ha : a ^ q.order = -a) :
    CFSG.Models.Chevalley.fixedSubgroup CFSGTwistedA2OriginalRelations.A
      (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order) :=
  fixedElementOfNaturalUnit q (highest (q.Extension 2) a) (highest_unit_fixed q a ha)

def oppositeFixed (q : CFSG.PrimePower) (a : q.Extension 2) (ha : a ^ q.order = -a) :
    CFSG.Models.Chevalley.fixedSubgroup CFSGTwistedA2OriginalRelations.A
      (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order) :=
  fixedElementOfNaturalUnit q (opposite (q.Extension 2) a) (opposite_unit_fixed q a ha)

end SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
