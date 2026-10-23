import SymmetricSubgroupAsymptotics.CFSGTwistedDAnisotropicNormForm
import SymmetricSubgroupAsymptotics.CFSGQuadraticFixedCoefficients

/-! Literal linear norm-plane isometries are norm-one multiplication,
possibly followed by the actual quadratic field conjugation. The proof
uses one genuine nonfixed element, its norm/trace polynomial, and the
proved fixed-field coefficients; it applies in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNormPlaneIsometries
open CFSGTwistedDAnisotropicNormForm CFSGTwistedDLinearParameters
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists

theorem one_fixed_classification (q : CFSG.PrimePower)
    (T : q.Extension 2 ≃ₗ[fixedField q] q.Extension 2)
    (hT : ∀ a, normForm q (T a) = normForm q a) (h1 : T 1 = 1) :
    (∀ a, T a = a) ∨ (∀ a, T a = definingFieldAutomorphism q 2 a) := by
  let sigma := definingFieldAutomorphism q 2
  obtain ⟨theta, htheta⟩ := CFSGTwistedAQuadraticTrace.exists_nonfixed q
  have hs : ∀ a, sigma (sigma a) = a := CFSGTwistedANaturalMatrices.extension_two_pow_twice q
  have hB (a b : q.Extension 2) :
      (normForm q).polarBilin (T a) (T b) = (normForm q).polarBilin a b := by
    change normForm q (T a + T b) - normForm q (T a) - normForm q (T b) =
      normForm q (a + b) - normForm q a - normForm q b
    rw [← T.map_add, hT, hT, hT]
  have htrace := congrArg (fun x : fixedField q => (x : q.Extension 2)) (hB 1 theta)
  dsimp only at htrace
  rw [h1] at htrace
  rw [polar_coe, polar_coe] at htrace
  simp only [map_one, one_mul, mul_one] at htrace
  change sigma (T theta) + T theta = sigma theta + theta at htrace
  have hnorm := congrArg (fun x : fixedField q => (x : q.Extension 2)) (hT theta)
  dsimp only at hnorm
  rw [normForm_apply, normForm_apply, norm_coe, norm_coe] at hnorm
  change T theta * sigma (T theta) = theta * sigma theta at hnorm
  have hp : (T theta - theta) * (T theta - sigma theta) = 0 := by
    linear_combination (T theta) * htrace - hnorm
  have hcases : T theta = theta ∨ T theta = sigma theta := by
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hcoeff (a : q.Extension 2) :
      ∃ c d : fixedField q, a = c • (1 : q.Extension 2) + d • theta := by
    obtain ⟨c, d, he⟩ := CFSGQuadraticFixedCoefficients.exists_subfield_coefficients
      sigma hs theta htheta (fixedField q) (fun _ => Iff.rfl) a
    refine ⟨c, d, ?_⟩
    change a = c.val * 1 + d.val * theta
    rw [he]
    ring
  rcases hcases with ht | ht
  · left
    intro a
    obtain ⟨c, d, ha⟩ := hcoeff a
    calc
      T a = c • T 1 + d • T theta := by rw [ha, map_add, T.map_smul, T.map_smul]
      _ = a := by rw [h1, ht]; exact ha.symm
  · right
    intro a
    obtain ⟨c, d, ha⟩ := hcoeff a
    have hc : sigma c.val = c.val := c.property
    have hd : sigma d.val = d.val := d.property
    calc
      T a = c • T 1 + d • T theta := by rw [ha, map_add, T.map_smul, T.map_smul]
      _ = sigma a := by
        rw [h1, ht, ha]
        change c.val * 1 + d.val * sigma theta = sigma (c.val * 1 + d.val * theta)
        rw [map_add, map_mul, map_mul, map_one, hc, hd]

theorem scalar_classification (q : CFSG.PrimePower)
    (T : q.Extension 2 ≃ₗ[fixedField q] q.Extension 2)
    (hT : ∀ a, normForm q (T a) = normForm q a) :
    ∃ c : q.Extension 2, c ≠ 0 ∧ Algebra.norm (fixedField q) c = 1 ∧
      ((∀ a, T a = c * a) ∨ (∀ a, T a = c * definingFieldAutomorphism q 2 a)) := by
  let c := T 1
  have hc : c ≠ 0 := by
    intro he
    have h := T.injective (he.trans T.map_zero.symm)
    exact one_ne_zero h
  have hNc : Algebra.norm (fixedField q) c = 1 := by
    have h := hT 1
    rw [normForm_apply, normForm_apply] at h
    change Algebra.norm (fixedField q) c = Algebra.norm (fixedField q) 1 at h
    rw [map_one (Algebra.norm (fixedField q))] at h
    exact h
  let U : q.Extension 2 ≃ₗ[fixedField q] q.Extension 2 :=
    T.trans (Units.mulLeftLinearEquiv (fixedField q) (q.Extension 2) (Units.mk0 c hc)⁻¹)
  have hU (a : q.Extension 2) : U a = c⁻¹ * T a := rfl
  have hU1 : U 1 = 1 := by
    rw [hU]
    exact inv_mul_cancel₀ hc
  have hNU (a : q.Extension 2) : normForm q (U a) = normForm q a := by
    rw [hU, normForm_apply, normForm_apply, map_mul, Algebra.norm_inv, hNc, inv_one, one_mul]
    simpa only [normForm_apply] using hT a
  have hTU (a : q.Extension 2) : T a = c * U a := by
    rw [hU, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  refine ⟨c, hc, hNc, ?_⟩
  rcases one_fixed_classification q U hNU hU1 with h | h
  · exact Or.inl (fun a => (hTU a).trans (congrArg (fun z => c * z) (h a)))
  · exact Or.inr (fun a => (hTU a).trans (congrArg (fun z => c * z) (h a)))

end SymmetricSubgroupAsymptotics.CFSGTwistedDNormPlaneIsometries
