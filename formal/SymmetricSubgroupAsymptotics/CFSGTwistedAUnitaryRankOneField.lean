import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLowerOpposite
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairedRootJoin
import Mathlib.Algebra.Field.Subfield.Basic

/-! The actual rank-one defining-fixed equation is entrywise field
fixedness. The lift below is to SL2 over the literal fixed subfield of
the defining automorphism, not an assumed identification of named groups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists

theorem signedReversal_rank_one (K : Type) [Field K] :
    (signedReversalUnit K 1 : Mat K 1) = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signedReversalUnit_apply, signWeight, Fin.rev, Fin.ext_iff]

theorem rank_one_diagramField_val (K : Type) [Field K] (f : K →+* K)
    (u : NaturalElementary K 1) :
    (diagramFieldUnitHom K 1 f u.val : Mat K 1) = f.mapMatrix (u.val : Mat K 1) := by
  have hi : (↑(u.val⁻¹) : Mat K 1) =
      !![(u.val : Mat K 1) 1 1, -(u.val : Mat K 1) 0 1;
        -(u.val : Mat K 1) 1 0, (u.val : Mat K 1) 0 0] := by
    have hm := congrArg Subtype.val (map_inv (naturalToSpecialLinear K 1) u)
    change (↑(u.val⁻¹) : Mat K 1) = ((naturalToSpecialLinear K 1 u)⁻¹).val at hm
    have hs := congrArg Subtype.val
      (Matrix.SpecialLinearGroup.SL2_inv_expl (naturalToSpecialLinear K 1 u))
    change ((naturalToSpecialLinear K 1 u)⁻¹).val =
      !![(u.val : Mat K 1) 1 1, -(u.val : Mat K 1) 0 1;
        -(u.val : Mat K 1) 1 0, (u.val : Mat K 1) 0 0] at hs
    exact hm.trans hs
  rw [diagramFieldUnitHom_val, signedReversalUnit_inv_eq_transpose,
    signedReversal_rank_one, hi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.cons_val_zero]

theorem rank_one_fixed_entry (q : CFSG.PrimePower) (g : naturalFixed 1 q)
    (i j : Fin 2) :
    definingFieldAutomorphism q 2 ((g.val.val : Mat (q.Extension 2) 1) i j) =
      (g.val.val : Mat (q.Extension 2) 1) i j := by
  have he := congrArg (fun u : (Mat (q.Extension 2) 1)ˣ => (u : Mat (q.Extension 2) 1))
    g.property
  change (diagramFieldUnitHom (q.Extension 2) 1 (definingFieldAutomorphism q 2).toRingHom
    g.val.val : Mat (q.Extension 2) 1) = (g.val.val : Mat (q.Extension 2) 1) at he
  rw [rank_one_diagramField_val] at he
  exact congrArg (fun A : Mat (q.Extension 2) 1 => A i j) he

def rankOneFixedField (q : CFSG.PrimePower) : Subfield (q.Extension 2) :=
  (definingFieldAutomorphism q 2).toRingHom.eqLocusField (RingHom.id (q.Extension 2))

def rankOneFixedSL (q : CFSG.PrimePower) (g : naturalFixed 1 q) :
    Matrix.SpecialLinearGroup (Fin 2) (rankOneFixedField q) :=
  ⟨(fun i j => ⟨(g.val.val : Mat (q.Extension 2) 1) i j, rank_one_fixed_entry q g i j⟩), by
    rw [Matrix.det_fin_two]
    apply Subtype.ext
    change (g.val.val : Mat (q.Extension 2) 1) 0 0 *
      (g.val.val : Mat (q.Extension 2) 1) 1 1 -
      (g.val.val : Mat (q.Extension 2) 1) 0 1 *
      (g.val.val : Mat (q.Extension 2) 1) 1 0 = 1
    have hd := naturalElementary_det (q.Extension 2) 1 g.val
    change Matrix.det (g.val.val : Matrix (Fin 2) (Fin 2) (q.Extension 2)) = 1 at hd
    rw [Matrix.det_fin_two] at hd
    exact hd⟩

theorem rankOneFixedSL_map (q : CFSG.PrimePower) (g : naturalFixed 1 q) :
    Matrix.SpecialLinearGroup.map (rankOneFixedField q).subtype (rankOneFixedSL q g) =
      naturalToSpecialLinear (q.Extension 2) 1 g.val := by
  apply Subtype.ext
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
