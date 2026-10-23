import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarRadicalLine
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairedMonomial
import SymmetricSubgroupAsymptotics.CFSGMonomialUnitRootAction

/-! The fourth two-plane-star entry is a conjugate of the SAME actual
central root by the checked endpoint-paired Weyl word. Its minus sign
is retained explicitly, uniformly including the rank-three middle SL2
case and characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical CFSGMonomialUnitRootAction

theorem endpointPairWeyl_star_monomial (q : CFSG.PrimePower) (s : ℕ) :
    ((endpointPairWeyl q s).val.val : Mat (q.Extension 2) (s + 3)) =
      CFSGTypeAMonomialMatrices.monomial
        (pairPermutation (starPositive s 0) (starPositive s 1) (starNegative s 1) (starNegative s 0))
        (pairWeights (K := q.Extension 2) (starPositive s 0) (starNegative s 1)) := by
  have hp : (endpointNode s).castSucc = starPositive s 0 := Fin.ext rfl
  have hq : (endpointNode s).succ = starPositive s 1 := Fin.ext rfl
  have hr : (endpointNode s).rev.castSucc = starNegative s 1 := by
    apply Fin.ext
    simp only [endpointNode, Fin.val_castSucc, Fin.val_rev, starNegative,
      starPositive, CFSGTwistedAFirstBlock.head]
    omega
  have ht : (endpointNode s).rev.succ = starNegative s 0 := by
    apply Fin.ext
    simp only [endpointNode, Fin.val_succ, Fin.val_rev, starNegative,
      starPositive, CFSGTwistedAFirstBlock.head]
    omega
  simpa only [hp, hq, hr, ht] using endpointPairWeyl_monomial q s

def starSecondAxisFixed (q : CFSG.PrimePower) (s : ℕ)
    (c : centralParameters q (s + 1)) : naturalFixed (s + 3) q :=
  endpointPairWeyl q s *
    centralFixed q (s + 1) (-c.val)
      (centralParameters_condition q (s + 1) _ ((centralParameters q (s + 1)).neg_mem c.property)) *
    (endpointPairWeyl q s)⁻¹

theorem starSecondAxisFixed_matrix (q : CFSG.PrimePower) (s : ℕ)
    (c : centralParameters q (s + 1)) :
    ((starSecondAxisFixed q s c).val.val : Mat (q.Extension 2) (s + 3)) =
      1 + Matrix.single (starPositive s 1) (starNegative s 1) c.val := by
  let p := starPositive s 0
  let t := starPositive s 1
  let v := starNegative s 1
  let w := starNegative s 0
  have hpt : p ≠ t := (starPositive_injective s).ne (by decide)
  have hvw : v ≠ w := (starNegative_injective s).ne (by decide)
  have hpv : p ≠ v := (star_coordinates_disjoint s 1 0).symm
  have hpw : p ≠ w := (star_coordinates_disjoint s 0 0).symm
  have htv : t ≠ v := (star_coordinates_disjoint s 1 1).symm
  have htw : t ≠ w := (star_coordinates_disjoint s 0 1).symm
  let e := pairPermutation p t v w
  let d := pairWeights (K := q.Extension 2) p v
  have heT : e t = p := by
    simp only [e, pairPermutation, Equiv.trans_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hpv hpw]
  have heV : e v = w := by
    simp only [e, pairPermutation, Equiv.trans_apply,
      Equiv.swap_apply_of_ne_of_ne hpv.symm htv.symm, Equiv.swap_apply_left]
  have hesP : e.symm p = t := by
    apply e.injective
    rw [Equiv.apply_symm_apply, heT]
  have hesW : e.symm w = v := by
    apply e.injective
    rw [Equiv.apply_symm_apply, heV]
  have hdT : d t = 1 := by simp [d, pairWeights, hpt.symm, htv]
  have hdV : d v = -1 := by simp [d, pairWeights]
  have hmono := endpointPairWeyl_star_monomial q s
  change ((endpointPairWeyl q s).val.val : Mat (q.Extension 2) (s + 3)) =
    CFSGTypeAMonomialMatrices.monomial e d at hmono
  have hh := monomial_conjugation (endpointPairWeyl q s).val.val e d hmono hpw (-c.val)
    (pairWeights_ne_zero p v (e.symm w))
  have hm := congrArg (fun g : (Mat (q.Extension 2) (s + 3))ˣ => (g : Mat (q.Extension 2) (s + 3))) hh
  have hcond : Condition q (s + 1) 0 (-c.val) :=
    centralParameters_condition q (s + 1) _ ((centralParameters q (s + 1)).neg_mem c.property)
  have hc : ((centralFixed q (s + 1) (-c.val) hcond).val.val : Mat (q.Extension 2) (s + 3)) =
      Matrix.transvection p w (-c.val) := radicalCentral_matrix q (s + 1) (-c.val) hcond
  change (((endpointPairWeyl q s).val.val : Mat (q.Extension 2) (s + 3)) *
      ((centralFixed q (s + 1) (-c.val) hcond).val.val : Mat (q.Extension 2) (s + 3)) *
      (↑((endpointPairWeyl q s).val.val⁻¹) : Mat (q.Extension 2) (s + 3))) = _
  rw [hc]
  simpa only [Units.val_mul, transvectionUnit_val, hesP, hesW, hdT, hdV,
    one_mul, neg_div_neg_eq, div_one, Matrix.transvection] using hm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
