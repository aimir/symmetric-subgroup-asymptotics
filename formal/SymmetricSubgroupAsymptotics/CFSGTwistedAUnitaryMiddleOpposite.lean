import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOuterWeyl
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalMiddleAction

/-! The literal middle embedding intertwines the SAME signed reversals,
hence carries the actual smaller upper/opposite join into the larger
one. This is needed for Gaussian induction without assuming that either
global reversal is already generated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryNaturalRadical

theorem blockFixedMatrixHom_reversal (q : CFSG.PrimePower) (s : ℕ) :
    (blockFixedMatrixHom q s (reversalFixed q (s + 2)) :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) =
      blockForm (parity q s) (middleForm q s) := by
  change (signedReversalUnit (q.Extension 2) (s + 2) : Mat (q.Extension 2) (s + 2)).submatrix
    (splitIndex s) (splitIndex s) = _
  exact signedForm_split (q.Extension 2) s

theorem reversal_middle_conjugate (q : CFSG.PrimePower) (s : ℕ) (A : naturalFixed s q) :
    reversalFixed q (s + 2) * naturalFixedMiddleHom q s A *
      (reversalFixed q (s + 2))⁻¹ =
        naturalFixedMiddleHom q s (reversalFixed q s * A * (reversalFixed q s)⁻¹) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply blockFixedMatrixHom_injective q s
  simp only [map_mul, blockFixedMatrixHom_middle]
  have hmiddle (B C : (Mat (q.Extension 2) s)ˣ) :
      middleUnit B * middleUnit C = middleUnit (B * C) :=
    (map_mul (middleUnitHom (K := q.Extension 2) (J := Fin (s + 1))) B C).symm
  simp only [hmiddle]
  apply Units.ext
  change (blockFixedMatrixHom q s (reversalFixed q (s + 2)) :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) *
      middleArray (A.val.val : Mat (q.Extension 2) s) =
    middleArray ((signedReversalUnit (q.Extension 2) s : Mat (q.Extension 2) s) *
      (A.val.val : Mat (q.Extension 2) s) *
        (↑((signedReversalUnit (q.Extension 2) s)⁻¹) : Mat (q.Extension 2) s)) *
      (blockFixedMatrixHom q s (reversalFixed q (s + 2)) :
        Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2))
  rw [blockFixedMatrixHom_reversal, blockForm_mul_middleArray, middleArray_mul_blockForm]
  congr 1
  simp only [middleForm, neg_mul, mul_neg, mul_assoc, Units.inv_mul, mul_one]

theorem middle_opposite_mem (q : CFSG.PrimePower) (s : ℕ)
    (g : NaturalElementary (q.Extension 2) s)
    (hg : g ∈ oppositeNaturalUnipotent q s) :
    naturalMiddleHom (q.Extension 2) s g ∈ oppositeNaturalUnipotent q (s + 2) := by
  obtain ⟨u, hu, rfl⟩ := hg
  let U : naturalFixed s q := ⟨u, hu.2⟩
  have he := congrArg Subtype.val (reversal_middle_conjugate q s U)
  refine ⟨naturalMiddleHom (q.Extension 2) s u,
    (middleUnipotentHom q s ⟨u, hu⟩).property, ?_⟩
  exact he

theorem middle_join_le (q : CFSG.PrimePower) (s : ℕ) :
    naturalUpperOppositeJoin q s ≤
      (naturalUpperOppositeJoin q (s + 2)).comap (naturalMiddleHom (q.Extension 2) s) := by
  apply sup_le
  · intro u hu
    exact (show naturalUnipotent (s + 2) q ≤ naturalUpperOppositeJoin q (s + 2)
      from le_sup_left) (middleUnipotentHom q s ⟨u, hu⟩).property
  · intro g hg
    exact (show oppositeNaturalUnipotent q (s + 2) ≤ naturalUpperOppositeJoin q (s + 2)
      from le_sup_right) (middle_opposite_mem q s g hg)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
