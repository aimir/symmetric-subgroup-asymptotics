import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankOneField
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnitRootTwist

/-! Unconditional rank-one Gaussian base. Actual fixed-field SL2
elementary generation gives membership in the literal upper/opposite
join, including characteristic2 and the smallest prime power. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGSerreSquareZeroMatrix CFSGTypeAElementaryMatrices
open CFSGSerreOrdinaryTwists

def rankOneScalarHom (q : CFSG.PrimePower) :
    Matrix.SpecialLinearGroup (Fin 2) (rankOneFixedField q) →*
      NaturalElementary (q.Extension 2) 1 :=
  (specialLinearToNatural (q.Extension 2) 1).comp
    (Matrix.SpecialLinearGroup.map (rankOneFixedField q).subtype)

theorem rankOneRoot_fixed (q : CFSG.PrimePower) (neg : Bool) (a : rankOneFixedField q) :
    elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) 1) neg 0 a.val ∈
      naturalFixed 1 q := by
  have ht : diagramFieldUnitHom (q.Extension 2) 1 (definingFieldAutomorphism q 2).toRingHom
      (naturalRootUnit (q.Extension 2) 1 neg 0 a.val) =
        naturalRootUnit (q.Extension 2) 1 neg 0 a.val := by
    rw [CFSGTwistedA2UnitRootTwist.simpleUnit_twist, Fin.eq_zero (0 : Fin 1).rev]
    have ha : definingFieldAutomorphism q 2 a.val = a.val := a.property
    rw [ha]
  exact ht

theorem rankOneRoot_mem_join (q : CFSG.PrimePower) (neg : Bool) (a : rankOneFixedField q) :
    elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) 1) neg 0 a.val ∈
      naturalUpperOppositeJoin q 1 := by
  cases neg
  · exact (show naturalUnipotent 1 q ≤ naturalUpperOppositeJoin q 1 from le_sup_left)
      ⟨positive_root_upper q 1 0 a.val, rankOneRoot_fixed q false a⟩
  · let g : naturalFixed 1 q :=
      ⟨elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) 1) true 0 a.val,
        rankOneRoot_fixed q true a⟩
    apply (show oppositeNaturalUnipotent q 1 ≤ naturalUpperOppositeJoin q 1 from le_sup_right)
    apply lowerFixed_mem_opposite q 1 g
    · intro i j hij
      change (1 + a.val • negative (q.Extension 2) 1 0) i j = 0
      fin_cases i <;> fin_cases j <;>
        simp_all [negative, positive, Matrix.add_apply]
    · intro i
      change (1 + a.val • negative (q.Extension 2) 1 0) i i = 1
      fin_cases i <;>
        norm_num [negative, positive, Matrix.transpose_apply,
          Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply,
          Fin.ext_iff]

theorem rankOneScalarHom_elementary (q : CFSG.PrimePower) (i j : Fin 2)
    (hij : i ≠ j) (a : rankOneFixedField q) :
    rankOneScalarHom q (elementary hij a) ∈ naturalUpperOppositeJoin q 1 := by
  have hs : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := rfl
  have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    fin_cases i <;> fin_cases j <;> simp_all
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have he : rankOneScalarHom q (elementary hij a) =
        elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) 1) false 0 a.val := by
      apply Subtype.ext
      apply Units.ext
      change (rankOneFixedField q).subtype.mapMatrix
        (1 + Matrix.single (0 : Fin 2) 1 a) =
        1 + a.val • positive (q.Extension 2) 1 0
      rw [map_add, map_one]
      change 1 + (Matrix.single (0 : Fin 2) 1 a).map (rankOneFixedField q).subtype = _
      rw [Matrix.map_single]
      simp only [positive, Matrix.smul_single, smul_eq_mul, mul_one,
        Fin.castSucc_zero, hs, Subfield.subtype_apply]
    rw [he]
    exact rankOneRoot_mem_join q false a
  · have he : rankOneScalarHom q (elementary hij a) =
        elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) 1) true 0 a.val := by
      apply Subtype.ext
      apply Units.ext
      change (rankOneFixedField q).subtype.mapMatrix
        (1 + Matrix.single (1 : Fin 2) 0 a) =
        1 + a.val • negative (q.Extension 2) 1 0
      rw [map_add, map_one]
      change 1 + (Matrix.single (1 : Fin 2) 0 a).map (rankOneFixedField q).subtype = _
      rw [Matrix.map_single]
      simp only [negative, positive, Matrix.transpose_single,
        Matrix.smul_single, smul_eq_mul, mul_one,
        Fin.castSucc_zero, hs, Subfield.subtype_apply]
    rw [he]
    exact rankOneRoot_mem_join q true a

theorem rank_one_mem_join (q : CFSG.PrimePower) (g : naturalFixed 1 q) :
    g.val ∈ naturalUpperOppositeJoin q 1 := by
  let H := (naturalUpperOppositeJoin q 1).comap (rankOneScalarHom q)
  have htop : H = ⊤ := by
    apply CFSGTypeAElementaryGeneration.eq_top_of_elementary
    intro i j hij a
    exact rankOneScalarHom_elementary q i j hij a
  have hg : rankOneFixedSL q g ∈ H := by rw [htop]; trivial
  change specialLinearToNatural (q.Extension 2) 1
    (Matrix.SpecialLinearGroup.map (rankOneFixedField q).subtype (rankOneFixedSL q g)) ∈
      naturalUpperOppositeJoin q 1 at hg
  rw [rankOneFixedSL_map] at hg
  have he : specialLinearToNatural (q.Extension 2) 1
      (naturalToSpecialLinear (q.Extension 2) 1 g.val) = g.val :=
    (naturalSpecialLinearEquiv (q.Extension 2) 1).left_inv g.val
  rwa [he] at hg

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
