import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOuterWeyl
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryReversalRootAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairedRotation

/-! Both literal endpoint-paired root lines lie in the actual upper/
opposite join. The negative line is the proved signed-reversal conjugate
of the positive line, with the field involution and parameter retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists

theorem positive_root_upper (q : CFSG.PrimePower) (r : ℕ)
    (i : Fin r) (a : q.Extension 2) :
    naturalToSpecialLinear (q.Extension 2) r
      (CFSGSerreSquareZeroMatrix.elementaryRoot (q.Extension 2)
        (naturalRootUnit (q.Extension 2) r) false i a) ∈
      CFSGUpperUnitriangular.upperUnitriangular (q.Extension 2) (r + 1) := by
  constructor
  · intro j k hkj
    have hjk : j ≠ k := ne_of_gt hkj
    have hs : ¬ (i.castSucc = j ∧ i.succ = k) := by
      rintro ⟨rfl, rfl⟩
      change i.val + 1 < i.val at hkj
      omega
    change (1 + a • Matrix.single i.castSucc i.succ (1 : q.Extension 2)) j k = 0
    simp only [Matrix.add_apply, Matrix.one_apply, if_neg hjk, Matrix.smul_apply,
      Matrix.single_apply, if_neg hs, smul_zero, add_zero]
  · intro j
    have hs : ¬ (i.castSucc = j ∧ i.succ = j) := by
      rintro ⟨hi, hj⟩
      have hv := congrArg (fun k : Fin (r + 1) => k.val) (hi.trans hj.symm)
      change i.val = i.val + 1 at hv
      omega
    change (1 + a • Matrix.single i.castSucc i.succ (1 : q.Extension 2)) j j = 1
    simp only [Matrix.add_apply, Matrix.one_apply, if_true, Matrix.smul_apply,
      Matrix.single_apply, if_neg hs, smul_zero, add_zero]

theorem endpointPositive_mem_upper (q : CFSG.PrimePower) (s : ℕ)
    (a : q.Extension 2) :
    (endpointNaturalFixedPair q s false a).val ∈ naturalUnipotent (s + 3) q := by
  constructor
  · exact (CFSGUpperUnitriangular.upperUnitriangular (q.Extension 2) (s + 4)).mul_mem
      (positive_root_upper q (s + 3) (endpointNode s) a)
      (positive_root_upper q (s + 3) (endpointNode s).rev
        (definingFieldAutomorphism q 2 a))
  · exact (endpointNaturalFixedPair q s false a).property

theorem endpointNegative_mem_opposite (q : CFSG.PrimePower) (s : ℕ)
    (a : q.Extension 2) :
    (endpointNaturalFixedPair q s true a).val ∈ oppositeNaturalUnipotent q (s + 3) := by
  let b := -(definingFieldAutomorphism q 2 a)
  have he := reversal_conjugate_endpointPair q s false b
  have haa : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 a) = a :=
    extension_two_pow_twice q a
  have hb : -(definingFieldAutomorphism q 2 b) = a := by
    dsimp only [b]
    rw [map_neg, haa, neg_neg]
  simp only [Bool.not_false, hb] at he
  exact ⟨(endpointNaturalFixedPair q s false b).val,
    endpointPositive_mem_upper q s b, congrArg Subtype.val he⟩

theorem endpointPair_mem_join (q : CFSG.PrimePower) (s : ℕ)
    (neg : Bool) (a : q.Extension 2) :
    (endpointNaturalFixedPair q s neg a).val ∈ naturalUpperOppositeJoin q (s + 3) := by
  cases neg
  · exact (show naturalUnipotent (s + 3) q ≤ naturalUpperOppositeJoin q (s + 3)
      from le_sup_left) (endpointPositive_mem_upper q s a)
  · exact (show oppositeNaturalUnipotent q (s + 3) ≤ naturalUpperOppositeJoin q (s + 3)
      from le_sup_right) (endpointNegative_mem_opposite q s a)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
