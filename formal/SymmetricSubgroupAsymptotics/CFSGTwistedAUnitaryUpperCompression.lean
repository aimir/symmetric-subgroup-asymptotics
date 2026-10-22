import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperMiddleArrays
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalKernel

/-! Actual middle compression of the literal defining-fixed upper group.
The compressed matrix is proved upper-unitriangular, determinant1 and
fixed by the ORIGINAL smaller signed diagram-field equation. No full SU
identification or inductive derived-membership assumption is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryNaturalRadical
open CFSGSerreOrdinaryTwists

def middleIndex (s : ℕ) (i : Fin (s + 1)) : Fin (s + 3) := splitIndex s (.inr (.inl i))

def middleBlock {K : Type} (s : ℕ) (A : Mat K (s + 2)) : Mat K s :=
  A.submatrix (middleIndex s) (middleIndex s)

theorem middleBlock_upper {K : Type} [Field K] (s : ℕ) (A : Mat K (s + 2))
    (hA : A.BlockTriangular id) : (middleBlock s A).BlockTriangular id := by
  intro i j hij
  apply hA
  change j.val < i.val at hij
  change j.val + 1 < i.val + 1
  omega

theorem middleBlock_diag {K : Type} [Field K] (s : ℕ) (A : Mat K (s + 2))
    (hA : ∀ i, A i i = 1) (i : Fin (s + 1)) : middleBlock s A i i = 1 := hA _

theorem middleBlock_det {K : Type} [Field K] (s : ℕ) (A : Mat K (s + 2))
    (hA : A.BlockTriangular id) (hd : ∀ i, A i i = 1) : (middleBlock s A).det = 1 := by
  rw [Matrix.det_of_upperTriangular (middleBlock_upper s A hA)]
  simp only [middleBlock_diag s A hd, Finset.prod_const_one]

theorem upper_block_shape {K : Type} [Field K] (s : ℕ) (A : Mat K (s + 2))
    (hA : A.BlockTriangular id) (hd : ∀ i, A i i = 1) :
    Matrix.reindex (splitEquiv s).symm (splitEquiv s).symm A =
      upperMiddleArray (fun i => A 0 (middleIndex s i)) (middleBlock s A)
        (fun i => A (middleIndex s i) (Fin.last (s + 2))) (A 0 (Fin.last (s + 2))) := by
  ext (u | (i | u)) (v | (j | v))
  all_goals try cases u
  all_goals try cases v
  all_goals simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    upperMiddleArray, splitEquiv, Equiv.coe_fn_mk, splitIndex, middleBlock, middleIndex]
  all_goals try rfl
  all_goals try exact hd _
  all_goals apply hA
  all_goals change _ < _
  all_goals simp only [id_eq, Fin.lt_def, Fin.val_zero, Fin.val_last, Fin.val_mk]
  all_goals try have hi := i.isLt
  all_goals try have hj := j.isLt
  all_goals omega

def middleNaturalElement (q : CFSG.PrimePower) (s : ℕ) (g : naturalUnipotent (s + 2) q) :
    NaturalElementary (q.Extension 2) s :=
  specialLinearToNatural (q.Extension 2) s
    ⟨middleBlock s (g.val.val : Mat (q.Extension 2) (s + 2)),
      middleBlock_det s _ g.property.1.1 g.property.1.2⟩

theorem middleNaturalElement_upper (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalUnipotent (s + 2) q) :
    naturalToSpecialLinear (q.Extension 2) s (middleNaturalElement q s g) ∈
      CFSGUpperUnitriangular.upperUnitriangular (q.Extension 2) (s + 1) :=
  ⟨middleBlock_upper s _ g.property.1.1, middleBlock_diag s _ g.property.1.2⟩

theorem middleNaturalElement_fixed (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalUnipotent (s + 2) q) : middleNaturalElement q s g ∈ naturalFixed s q := by
  have hs := blockFixedMatrixHom_isometry q s ⟨g.val, g.property.2⟩
  change ((Matrix.reindex (splitEquiv s).symm (splitEquiv s).symm
    (g.val.val : Mat (q.Extension 2) (s + 2))).map (definingFieldAutomorphism q 2)).transpose *
      blockForm (parity q s) (middleForm q s) *
        Matrix.reindex (splitEquiv s).symm (splitEquiv s).symm
          (g.val.val : Mat (q.Extension 2) (s + 2)) = blockForm (parity q s) (middleForm q s) at hs
  have hu : (g.val.val : Mat (q.Extension 2) (s + 2)).BlockTriangular id := g.property.1.1
  have hd : ∀ i, (g.val.val : Mat (q.Extension 2) (s + 2)) i i = 1 := g.property.1.2
  rw [upper_block_shape s (g.val.val : Mat (q.Extension 2) (s + 2)) hu hd] at hs
  have hm := upperMiddleArray_isometry_middle (definingFieldAutomorphism q 2).toRingHom
    (parity q s) (middleForm q s) (middleBlock s (g.val.val : Mat (q.Extension 2) (s + 2))) _ _ _ hs
  change diagramFieldUnitHom (q.Extension 2) s (definingFieldAutomorphism q 2).toRingHom
    (middleNaturalElement q s g).val = _
  apply unit_fixed_of_signedForm (q.Extension 2) s (definingFieldAutomorphism q 2).toRingHom
  change ((middleBlock s (g.val.val : Mat (q.Extension 2) (s + 2))).map
    (definingFieldAutomorphism q 2)).transpose * (signedReversalUnit (q.Extension 2) s : Mat (q.Extension 2) s) *
      middleBlock s (g.val.val : Mat (q.Extension 2) (s + 2)) = _
  simpa only [middleForm, mul_neg, neg_mul, neg_neg] using congrArg Neg.neg hm

def middleUnipotentElement (q : CFSG.PrimePower) (s : ℕ) (g : naturalUnipotent (s + 2) q) :
    naturalUnipotent s q :=
  ⟨middleNaturalElement q s g, middleNaturalElement_upper q s g, middleNaturalElement_fixed q s g⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
