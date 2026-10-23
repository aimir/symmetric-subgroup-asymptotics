import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoDerivedCover
import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusFixed
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! The complete quadratic-field unit torus, as a literal homomorphism
into the same natural fixed matrices and original central quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGTwistedA2DiagonalTorus

def rankTwoNaturalTorus (q : CFSG.PrimePower) :
    (q.Extension 2)ˣ →* naturalFixed 2 q where
  toFun z := ⟨torusNatural (q.Extension 2) (definingFieldAutomorphism q 2) z,
    torusNatural_fixed (q.Extension 2) (definingFieldAutomorphism q 2)
      (fun x => extension_two_pow_twice q x) z (Units.ne_zero z)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change ((torusNatural (q.Extension 2) (definingFieldAutomorphism q 2) 1).val :
      Mat (q.Extension 2) 2) = 1
    rw [torusNatural_val _ _ 1 one_ne_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [torusWeights, Matrix.diagonal]
  map_mul' z w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change ((torusNatural (q.Extension 2) (definingFieldAutomorphism q 2)
      ((z : q.Extension 2) * w)).val : Mat (q.Extension 2) 2) =
      ((torusNatural (q.Extension 2) (definingFieldAutomorphism q 2) z).val : Mat _ 2) *
        ((torusNatural (q.Extension 2) (definingFieldAutomorphism q 2) w).val : Mat _ 2)
    rw [torusNatural_val _ _ _ (mul_ne_zero (Units.ne_zero z) (Units.ne_zero w)),
      torusNatural_val _ _ _ (Units.ne_zero z), torusNatural_val _ _ _ (Units.ne_zero w),
      Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i <;> simp [torusWeights, map_mul, mul_div_mul_comm, mul_inv_rev, mul_comm]

def rankTwoProjectiveCover (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    naturalFixed 2 q →* CFSG.Models.TwistedA 2 q :=
  (QuotientGroup.mk' (Subgroup.center (commutator (Fixed 2 q)))).comp
    (rankTwoDerivedCover q hq)

theorem rankTwoProjectiveCover_surjective (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Function.Surjective (rankTwoProjectiveCover q hq) :=
  (QuotientGroup.mk'_surjective _).comp (rankTwoDerivedCover_surjective q hq)

def rankTwoProjectiveTorus (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (q.Extension 2)ˣ →* CFSG.Models.TwistedA 2 q :=
  (rankTwoProjectiveCover q hq).comp (rankTwoNaturalTorus q)

theorem rankTwoNaturalTorus_matrix (q : CFSG.PrimePower) (z : (q.Extension 2)ˣ) :
    (((rankTwoNaturalTorus q z).val).val : Mat (q.Extension 2) 2) =
      Matrix.diagonal (torusWeights (q.Extension 2) (definingFieldAutomorphism q 2) z) :=
  torusNatural_val _ _ _ (Units.ne_zero z)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
