import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLowerOpposite
import SymmetricSubgroupAsymptotics.CFSGTwistedA2IsometricGeneration
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentScalarRigidity

/-! The already proved raw rank-two Gaussian generation is installed in
the current literal signed-reversal upper/opposite join. This raw matrix
base holds for ALL q, including SU3(2); it makes no assertion that this
small fixed group is perfect or that its own U lies in its derived group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryNaturalRadical

theorem rankTwoOldUpper_le (q : CFSG.PrimePower) :
    CFSGTwistedA2UnipotentArrays.naturalUnipotent q ≤ naturalUnipotent 2 q := by
  rintro u ⟨a, b, hab, rfl⟩
  constructor
  · constructor
    · change (CFSGTwistedA2UnipotentArrays.upperNatural (q.Extension 2)
        (definingFieldAutomorphism q 2) a b).val.val.BlockTriangular id
      rw [CFSGTwistedA2UnipotentArrays.upperNatural_val]
      exact CFSGTwistedA2UnipotentArrays.upperArray_upper (definingFieldAutomorphism q 2) a b
    · intro i
      change ((CFSGTwistedA2UnipotentArrays.upperNatural (q.Extension 2)
        (definingFieldAutomorphism q 2) a b).val : Mat (q.Extension 2) 2) i i = 1
      rw [CFSGTwistedA2UnipotentArrays.upperNatural_val]
      exact CFSGTwistedA2UnipotentArrays.upperArray_diagonal (definingFieldAutomorphism q 2) a b i
  · exact CFSGTwistedA2UnipotentArrays.upperNatural_fixed (q.Extension 2)
      (definingFieldAutomorphism q 2) (fun x => extension_two_pow_twice q x) a b hab

theorem rankTwoOldOpposite_le (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht0 : t ≠ 0) (ht : t ^ q.order = -t) :
    (CFSGTwistedA2UnipotentArrays.naturalUnipotent q).map
      (MulAut.conj (CFSGTwistedA2UnipotentArrays.weylNatural (q.Extension 2) t)).toMonoidHom ≤
        oppositeNaturalUnipotent q 2 := by
  rintro g ⟨u, hu, rfl⟩
  obtain ⟨a, b, hab, rfl⟩ := hu
  let g := CFSGTwistedA2UnipotentArrays.oppositeNatural (q.Extension 2)
    (definingFieldAutomorphism q 2) t a b
  have hfix : g ∈ naturalFixed 2 q := by
    change diagramFieldUnitHom (q.Extension 2) 2 (definingFieldAutomorphism q 2).toRingHom
      ((CFSGTwistedA2UnipotentArrays.weylNatural (q.Extension 2) t).val *
        (CFSGTwistedA2UnipotentArrays.upperNatural (q.Extension 2)
          (definingFieldAutomorphism q 2) a b).val *
        ((CFSGTwistedA2UnipotentArrays.weylNatural (q.Extension 2) t).val)⁻¹) = _
    rw [map_mul, map_mul, map_inv, CFSGTwistedA2UnipotentArrays.weylNatural_fixed q t ht,
      CFSGTwistedA2UnipotentArrays.upperNatural_fixed (q.Extension 2)
        (definingFieldAutomorphism q 2) (fun x => extension_two_pow_twice q x) a b hab]
    rfl
  apply lowerFixed_mem_opposite q 2 ⟨g, hfix⟩
  · intro i j hij
    change (g.val : Mat (q.Extension 2) 2) i j = 0
    rw [CFSGTwistedA2UnipotentArrays.oppositeNatural_array _ _ t ht0]
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  · intro i
    change (g.val : Mat (q.Extension 2) 2) i i = 1
    rw [CFSGTwistedA2UnipotentArrays.oppositeNatural_array _ _ t ht0]
    fin_cases i <;> simp [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rank_two_mem_join (q : CFSG.PrimePower) (g : naturalFixed 2 q) :
    g.val ∈ naturalUpperOppositeJoin q 2 := by
  obtain ⟨t, ht0, htc⟩ := exists_nonzero_central_parameter q 0
  have ht : t ^ q.order = -t := by
    change definingFieldAutomorphism q 2 t = -t
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [parity, pow_zero, one_mul] using (centralCondition_iff q 0 t).mp htc
  have hgen := CFSGTwistedA2UnipotentArrays.isometric_mem_rootGenerated q t ht0 ht g.val
    (fixed_unit_isometric (q.Extension 2) 2 (definingFieldAutomorphism q 2).toRingHom
      g.val.val g.property)
  have hle : CFSGTwistedA2UnipotentArrays.naturalRootGenerated q t ≤
      naturalUpperOppositeJoin q 2 :=
    sup_le ((rankTwoOldUpper_le q).trans
      (show naturalUnipotent 2 q ≤ naturalUpperOppositeJoin q 2 from le_sup_left))
      ((rankTwoOldOpposite_le q t ht0 ht).trans
        (show oppositeNaturalUnipotent q 2 ≤ naturalUpperOppositeJoin q 2 from le_sup_right))
  exact hle hgen

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
