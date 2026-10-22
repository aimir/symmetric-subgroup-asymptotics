import SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestFixedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentDerived
import Mathlib.LinearAlgebra.Matrix.Notation

/-! An actual original fixed-source Weyl word from the highest and
opposite root elements, with its literal natural three-dimensional matrix. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGTwistedA2OriginalRelations
open CFSGTwistedA2HighestRootUnits CFSGSerreOrdinaryTwists
variable (K : Type) [Field K]

def weylNatural (t : K) : NaturalElementary K 2 :=
  highest K t * opposite K (-t⁻¹) * highest K t

theorem highest_array (t : K) :
    ((highest K t).val : Mat K 2) = !![1, 0, t; 0, 1, 0; 0, 0, 1] := by
  rw [highest_val, entryUnit_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.add_apply, Matrix.one_apply, Matrix.single, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem opposite_array (t : K) :
    ((opposite K t).val : Mat K 2) = !![1, 0, 0; 0, 1, 0; t, 0, 1] := by
  rw [opposite_val, entryUnit_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.add_apply, Matrix.one_apply, Matrix.single, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem weylNatural_array (t : K) (ht : t ≠ 0) :
    ((weylNatural K t).val : Mat K 2) = !![0, 0, t; 0, 1, 0; -t⁻¹, 0, 0] := by
  change (((highest K t).val : Mat K 2) * ((opposite K (-t⁻¹)).val : Mat K 2)) *
    ((highest K t).val : Mat K 2) = _
  simp only [highest_array, opposite_array]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> field_simp [ht] <;> (try ring) <;> simp_all

theorem neg_inv_skew (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) : (-t⁻¹) ^ q.order = -(-t⁻¹) := by
  change definingFieldAutomorphism q 2 (-t⁻¹) = -(-t⁻¹)
  rw [map_neg, map_inv₀]
  change -(t ^ q.order)⁻¹ = -(-t⁻¹)
  rw [ht, inv_neg]

theorem weylNatural_fixed (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) :
    diagramFieldUnitHom (q.Extension 2) 2 (definingFieldAutomorphism q 2).toRingHom
      (weylNatural (q.Extension 2) t).val = (weylNatural (q.Extension 2) t).val := by
  change diagramFieldUnitHom (q.Extension 2) 2 (definingFieldAutomorphism q 2).toRingHom
    ((highest (q.Extension 2) t).val * (opposite (q.Extension 2) (-t⁻¹)).val *
      (highest (q.Extension 2) t).val) = _
  rw [map_mul, map_mul, highest_unit_fixed q t ht,
    opposite_unit_fixed q (-t⁻¹) (neg_inv_skew q t ht)]
  rfl

def originalWeyl (q : CFSG.PrimePower) (t : q.Extension 2) (ht : t ^ q.order = -t) :
    OriginalFixedA 2 q :=
  fixedElementOfNaturalUnit q (weylNatural (q.Extension 2) t) (weylNatural_fixed q t ht)

theorem originalWeyl_action (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) :
    twistedFixedAction 2 q (originalWeyl q t ht) =
      naturalElementaryAction (q.Extension 2) 2 (weylNatural (q.Extension 2) t) :=
  elementaryToModel_action (q.Extension 2) _

theorem originalWeyl_word (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) :
    originalWeyl q t ht = highestFixed q t ht *
      oppositeFixed q (-t⁻¹) (neg_inv_skew q t ht) * highestFixed q t ht := by
  apply fixedToModel_injective q
  change elementaryToModel (q.Extension 2) (weylNatural (q.Extension 2) t) =
    elementaryToModel (q.Extension 2) (highest (q.Extension 2) t) *
      elementaryToModel (q.Extension 2) (opposite (q.Extension 2) (-t⁻¹)) *
        elementaryToModel (q.Extension 2) (highest (q.Extension 2) t)
  exact (map_mul (elementaryToModel (q.Extension 2)) _ _).trans
    (congrArg (fun x => x * elementaryToModel (q.Extension 2) (highest (q.Extension 2) t))
      (map_mul (elementaryToModel (q.Extension 2)) _ _))

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
