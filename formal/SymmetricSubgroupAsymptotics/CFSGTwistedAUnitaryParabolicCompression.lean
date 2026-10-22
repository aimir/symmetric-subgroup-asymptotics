import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParabolicArrays
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperCompression
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadicalSupport

/-! Actual middle compression for a defining-fixed matrix whose first
column is e0. The determinant-one and smaller defining-fixed equations
are proved from the literal block shape, with no upper-triangular middle
or full-unitary hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryNaturalRadical
open CFSGSerreOrdinaryTwists

theorem normalized_first_block_column (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q)
    (hcol : (fun i => (g.val.val : Mat (q.Extension 2) (s + 2)) i 0) = Pi.single 0 1) :
    ∀ i, (blockFixedMatrixHom q s g :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) i (.inl ()) =
        if i = .inl () then 1 else 0 := by
  intro i
  rw [blockFixedMatrixHom_apply]
  have hx := congrFun hcol (splitEquiv s i)
  change (g.val.val : Mat (q.Extension 2) (s + 2)) (splitEquiv s i) 0 = _ at hx
  change (g.val.val : Mat (q.Extension 2) (s + 2)) (splitEquiv s i) 0 = _
  by_cases hi : i = .inl ()
  · subst i
    simpa only [splitEquiv, Equiv.coe_fn_mk, splitIndex, Pi.single_eq_same, if_true] using hx
  · have hne : splitEquiv s i ≠ (0 : Fin (s + 3)) := by
      intro he
      apply hi
      apply (splitEquiv s).injective
      exact he
    simpa only [Pi.single_apply, if_neg hne, if_neg hi] using hx

theorem normalized_block_shape (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q)
    (hcol : (fun i => (g.val.val : Mat (q.Extension 2) (s + 2)) i 0) = Pi.single 0 1) :
    (blockFixedMatrixHom q s g :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) =
      upperMiddleArray
        (fun i => (g.val.val : Mat (q.Extension 2) (s + 2)) 0 (middleIndex s i))
        (middleBlock s (g.val.val : Mat (q.Extension 2) (s + 2)))
        (fun i => (g.val.val : Mat (q.Extension 2) (s + 2)) (middleIndex s i) (Fin.last (s + 2)))
        ((g.val.val : Mat (q.Extension 2) (s + 2)) 0 (Fin.last (s + 2))) := by
  have hc := normalized_first_block_column q s g hcol
  have hr := isometry_first_column_last_row (definingFieldAutomorphism q 2).toRingHom
    (parity q s) (middleForm q s) _ (blockFixedMatrixHom_isometry q s g) hc
  exact parabolic_block_shape _ hc hr

theorem normalized_middle_det (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q)
    (hcol : (fun i => (g.val.val : Mat (q.Extension 2) (s + 2)) i 0) = Pi.single 0 1) :
    (middleBlock s (g.val.val : Mat (q.Extension 2) (s + 2))).det = 1 := by
  have hd : (blockFixedMatrixHom q s g :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)).det = 1 := by
    change (Matrix.reindex (splitEquiv s).symm (splitEquiv s).symm
      (g.val.val : Mat (q.Extension 2) (s + 2))).det = 1
    rw [Matrix.det_reindex_self]
    exact naturalElementary_det (q.Extension 2) (s + 2) g.val
  rw [normalized_block_shape q s g hcol, upperMiddleArray_det] at hd
  exact hd

def normalizedMiddleNatural (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q)
    (hcol : (fun i => (g.val.val : Mat (q.Extension 2) (s + 2)) i 0) = Pi.single 0 1) :
    NaturalElementary (q.Extension 2) s :=
  specialLinearToNatural (q.Extension 2) s
    ⟨middleBlock s (g.val.val : Mat (q.Extension 2) (s + 2)), normalized_middle_det q s g hcol⟩

theorem normalizedMiddleNatural_fixed (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q)
    (hcol : (fun i => (g.val.val : Mat (q.Extension 2) (s + 2)) i 0) = Pi.single 0 1) :
    normalizedMiddleNatural q s g hcol ∈ naturalFixed s q := by
  have hs := blockFixedMatrixHom_isometry q s g
  rw [normalized_block_shape q s g hcol] at hs
  have hm := upperMiddleArray_isometry_middle (definingFieldAutomorphism q 2).toRingHom
    (parity q s) (middleForm q s) (middleBlock s (g.val.val : Mat (q.Extension 2) (s + 2)))
    _ _ _ hs
  change diagramFieldUnitHom (q.Extension 2) s (definingFieldAutomorphism q 2).toRingHom
    (normalizedMiddleNatural q s g hcol).val = _
  apply unit_fixed_of_signedForm (q.Extension 2) s (definingFieldAutomorphism q 2).toRingHom
  change ((middleBlock s (g.val.val : Mat (q.Extension 2) (s + 2))).map
    (definingFieldAutomorphism q 2)).transpose * (signedReversalUnit (q.Extension 2) s : Mat (q.Extension 2) s) *
      middleBlock s (g.val.val : Mat (q.Extension 2) (s + 2)) = _
  simpa only [middleForm, mul_neg, neg_mul, neg_neg] using congrArg Neg.neg hm

def normalizedMiddleFixed (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q)
    (hcol : (fun i => (g.val.val : Mat (q.Extension 2) (s + 2)) i 0) = Pi.single 0 1) :
    naturalFixed s q :=
  ⟨normalizedMiddleNatural q s g hcol, normalizedMiddleNatural_fixed q s g hcol⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
