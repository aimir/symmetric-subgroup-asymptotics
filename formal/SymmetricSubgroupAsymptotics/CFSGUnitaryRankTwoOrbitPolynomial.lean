import SymmetricSubgroupAsymptotics.CFSGUnitaryIsotropicFirstOrbit

/-! A polynomial bound on the actual dimension-three first-point
orbit.  No enumeration or transitivity of all isotropic points is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianPolynomial
open CFSGTwistedANaturalMatrices

theorem normPolynomial_rank_two_ne_zero (q : CFSG.PrimePower) :
    normPolynomial q 2 ≠ 0 := by
  have hv : signedNorm q 2 ![0, 1, 0] = -1 := by
    norm_num [signedNorm, Fin.sum_univ_succ, signWeight, Fin.rev]
  intro hz
  have he : signedNorm q 2 ![0, 1, 0] = 0 := by
    rw [← eval_normPolynomial, hz]
    exact map_zero _
  exact (neg_ne_zero.mpr one_ne_zero) (hv.symm.trans he)

theorem firstPointOrbit_rank_two_card_mul_le (q : CFSG.PrimePower) :
    Nat.card (firstPointOrbit q 2) * (q.order - 1) ≤ q.order ^ 4 := by
  have hzero (p : firstPointOrbit q 2) (a : (q.Extension 2)ˣ) :
      MvPolynomial.eval (a • p.val.rep) (normPolynomial q 2) = 0 := by
    rw [eval_normPolynomial]
    change signedNorm q 2 ((a : q.Extension 2) • p.val.rep) = 0
    rw [signedNorm_smul, firstPointOrbit_rep_norm_zero q 2 (by decide), mul_zero]
  have hc := CFSGProjectivePolynomialCount.projective_polynomial_carrier_bound 2 (q.order + 1)
    (normPolynomial q 2) (normPolynomial_rank_two_ne_zero q) (normPolynomial_degree_le q 2)
    (firstPointOrbit q 2) hzero
  rw [extension_two_card] at hc
  have hq := CFSGTwistedAQuadraticTrace.order_two_le q
  have he : q.order ^ 2 - 1 = (q.order - 1) * (q.order + 1) := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ q.order by omega),
      Nat.sub_add_cancel (show 1 ≤ q.order ^ 2 by nlinarith)]
  rw [he, ← mul_assoc] at hc
  have hb : (Nat.card (firstPointOrbit q 2) * (q.order - 1)) * (q.order + 1) ≤
      q.order ^ 4 * (q.order + 1) := by
    simpa only [← pow_mul, Nat.mul_comm] using hc
  exact (mul_le_mul_iff_left₀ (Nat.succ_pos q.order)).mp hb

end SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianPolynomial
