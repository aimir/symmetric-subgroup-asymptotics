import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankOneGeneration
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import Mathlib.SetTheory.Cardinal.Finite

/-! Actual upper-subgroup cardinalities in the two Gaussian base ranks.
Rank one is parametrized by the literal Frobenius-fixed subfield. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedA2FixedField CFSGSerreSquareZeroMatrix

theorem naturalUnipotent_card_zero (q : CFSG.PrimePower) :
    Nat.card (naturalUnipotent 0 q) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨1, ?_⟩
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [Fin.eq_zero i, Fin.eq_zero j]
  exact g.property.1.2 0

def rankOneUpperParameter (q : CFSG.PrimePower) (g : naturalUnipotent 1 q) :
    fixedField q :=
  ⟨(g.val.val : Mat (q.Extension 2) 1) 0 1,
    rank_one_fixed_entry q ⟨g.val, g.property.2⟩ 0 1⟩

def rankOneUpperElement (q : CFSG.PrimePower) (t : fixedField q) : naturalUnipotent 1 q :=
  ⟨elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) 1) false 0 t.val,
    positive_root_upper q 1 0 t.val, rankOneRoot_fixed q false t⟩

theorem rankOneUpperParameter_element (q : CFSG.PrimePower) (t : fixedField q) :
    rankOneUpperParameter q (rankOneUpperElement q t) = t := by
  apply Subtype.ext
  change (1 + t.val • positive (q.Extension 2) 1 0) (0 : Fin 2) 1 = t.val
  norm_num [positive, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.single_apply, Fin.ext_iff]

theorem rankOneUpperElement_parameter (q : CFSG.PrimePower) (g : naturalUnipotent 1 q) :
    rankOneUpperElement q (rankOneUpperParameter q g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (1 + (g.val.val : Mat (q.Extension 2) 1) 0 1 •
      positive (q.Extension 2) 1 0) i j = (g.val.val : Mat (q.Extension 2) 1) i j
  have hd : ∀ i : Fin 2, (g.val.val : Mat (q.Extension 2) 1) i i = 1 := g.property.1.2
  have hz : (g.val.val : Mat (q.Extension 2) 1) 1 0 = 0 :=
    g.property.1.1 (by decide : (0 : Fin 2) < 1)
  fin_cases i <;> fin_cases j <;>
    norm_num [positive, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.single_apply, Fin.ext_iff, hd, hz]

def rankOneUpperEquiv (q : CFSG.PrimePower) : fixedField q ≃ naturalUnipotent 1 q where
  toFun := rankOneUpperElement q
  invFun := rankOneUpperParameter q
  left_inv := rankOneUpperParameter_element q
  right_inv := rankOneUpperElement_parameter q

theorem naturalUnipotent_card_one (q : CFSG.PrimePower) :
    Nat.card (naturalUnipotent 1 q) = q.order :=
  (Nat.card_congr (rankOneUpperEquiv q)).symm.trans (fixedField_card q)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
