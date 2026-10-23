import SymmetricSubgroupAsymptotics.CFSGUnitaryNormIsometry

/-! The actual first-point orbit lies on the literal Hermitian
polynomial. Its four-dimensional count uses Schwartz--Zippel and all
unit-scalar fibres, without a finite unitary action catalogue. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix

namespace SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianPolynomial
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryCoordinates
open CFSGProjectiveLinearPointAction CFSGProjectiveFrameCoordinates

def firstPointOrbit (q : CFSG.PrimePower) (r : ℕ) : Set (unitaryNaturalPoints q r) :=
  letI := unitaryNaturalPointAction q r
  MulAction.orbit (naturalFixed r q) (basisPoint (F := q.Extension 2) (0 : Fin (r + 1)))

theorem firstPointOrbit_rep_norm_zero (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r)
    (p : firstPointOrbit q r) : signedNorm q r p.val.rep = 0 := by
  letI := unitaryNaturalPointAction q r
  obtain ⟨g, hg⟩ := p.property
  change linearEquiv g.val.val • basisPoint (F := q.Extension 2) (0 : Fin (r + 1)) = p.val at hg
  rw [basisPoint, Projectivization.smul_mk] at hg
  rw [← hg]
  apply signedNorm_projective_rep_zero
  change signedNorm q r ((g.val.val : Mat (q.Extension 2) r) *ᵥ Pi.single 0 1) = 0
  rw [Matrix.mulVec_single_one]
  exact signedNorm_first_column_zero q r hr g

theorem firstPointOrbit_rank_three_card_le (q : CFSG.PrimePower) :
    Nat.card (firstPointOrbit q 3) ≤ q.order ^ 6 := by
  have hzero (p : firstPointOrbit q 3) (a : (q.Extension 2)ˣ) :
      MvPolynomial.eval (a • p.val.rep) (normPolynomial q 3) = 0 := by
    rw [eval_normPolynomial]
    change signedNorm q 3 ((a : q.Extension 2) • p.val.rep) = 0
    rw [signedNorm_smul, firstPointOrbit_rep_norm_zero q 3 (by omega), mul_zero]
  have hc := CFSGProjectivePolynomialCount.projective_polynomial_carrier_bound 3 (q.order + 1)
    (normPolynomial q 3) (normPolynomial_rank_three_ne_zero q) (normPolynomial_degree_le q 3)
    (firstPointOrbit q 3) hzero
  rw [extension_two_card] at hc
  have hq := CFSGTwistedAQuadraticTrace.order_two_le q
  have hd : q.order + 1 ≤ q.order ^ 2 - 1 := by
    nlinarith [Nat.sub_add_cancel (by nlinarith : 1 ≤ q.order ^ 2)]
  have hm := (Nat.mul_le_mul_left (Nat.card (firstPointOrbit q 3)) hd).trans hc
  have hb : Nat.card (firstPointOrbit q 3) * (q.order + 1) ≤ q.order ^ 6 * (q.order + 1) := by
    simpa only [← pow_mul, Nat.mul_comm] using hm
  exact (mul_le_mul_iff_left₀ (Nat.succ_pos q.order)).mp hb

end SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianPolynomial
