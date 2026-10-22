import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
import Mathlib.Data.Matrix.Mul

/-! Actual quadratic-extension parameters for signed Hermitian block
shears. Both the trace and skew-difference equations are soluble also at
q=2. The norm-reality lemma is symbolic in the middle-space dimension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParameters
open CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices CFSGTwistedAQuadraticTrace

theorem exists_sigma_sub_eq (q : CFSG.PrimePower) (c : q.Extension 2)
    (hc : definingFieldAutomorphism q 2 c = -c) :
    ∃ b : q.Extension 2, definingFieldAutomorphism q 2 b - b = c := by
  obtain ⟨t, ht, hts⟩ := exists_skew_nonzero q
  have hfixed : definingFieldAutomorphism q 2 (-c / t) = -c / t := by
    rw [map_div₀, map_neg, hc, hts, neg_neg, div_neg, neg_div]
  obtain ⟨a, ha⟩ := exists_trace_eq_fixed q (-c / t) hfixed
  refine ⟨t * a, ?_⟩
  rw [map_mul, hts]
  calc
    -t * definingFieldAutomorphism q 2 a - t * a =
        -t * (a + definingFieldAutomorphism q 2 a) := by ring
    _ = -t * (-c / t) := congrArg (fun z : q.Extension 2 => -t * z) ha
    _ = c := by field_simp [ht]

theorem exists_signedTrace_eq (q : CFSG.PrimePower) (eps c : q.Extension 2)
    (heps : eps = 1 ∨ eps = -1)
    (hc : definingFieldAutomorphism q 2 c = eps * c) :
    ∃ b : q.Extension 2, definingFieldAutomorphism q 2 b + eps * b = c := by
  rcases heps with rfl | rfl
  · obtain ⟨b, hb⟩ := exists_trace_eq_fixed q c (by simpa only [one_mul] using hc)
    exact ⟨b, by simpa only [one_mul, add_comm] using hb⟩
  · obtain ⟨b, hb⟩ := exists_sigma_sub_eq q c (by simpa only [neg_one_mul] using hc)
    exact ⟨b, by simpa only [neg_one_mul, sub_eq_add_neg] using hb⟩

def hermitianNorm {K J : Type*} [Field K] [Fintype J]
    (sigma : K ≃+* K) (H : Matrix J J K) (v : J → K) : K :=
  dotProduct (fun i => sigma (v i)) (H *ᵥ v)

theorem hermitianNorm_sigma {K J : Type*} [Field K] [Fintype J]
    (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x)
    (eps : K) (H : Matrix J J K) (hH : H.map sigma = eps • H.transpose) (v : J → K) :
    sigma (hermitianNorm sigma H v) = eps * hermitianNorm sigma H v := by
  change sigma.toRingHom (dotProduct (fun i => sigma (v i)) (H *ᵥ v)) = _
  rw [RingHom.map_dotProduct]
  have hv : sigma.toRingHom ∘ (fun i => sigma (v i)) = v := by
    funext i
    exact hsigma (v i)
  have hm : sigma.toRingHom ∘ (H *ᵥ v) = H.map sigma *ᵥ (sigma.toRingHom ∘ v) := by
    funext i
    exact RingHom.map_mulVec sigma.toRingHom H v i
  rw [hv, hm, hH, Matrix.smul_mulVec, dotProduct_smul,
    Matrix.dotProduct_transpose_mulVec]
  rfl

theorem exists_block_parameter {J : Type*} [Fintype J]
    (q : CFSG.PrimePower) (eps : q.Extension 2) (heps : eps = 1 ∨ eps = -1)
    (H : Matrix J J (q.Extension 2))
    (hH : H.map (definingFieldAutomorphism q 2) = eps • H.transpose)
    (v : J → q.Extension 2) :
    ∃ b : q.Extension 2, definingFieldAutomorphism q 2 b + eps * b =
      -hermitianNorm (definingFieldAutomorphism q 2) H v := by
  apply exists_signedTrace_eq q eps _ heps
  rw [map_neg, hermitianNorm_sigma _ (fun x => extension_two_pow_twice q x) eps H hH v]
  ring

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParameters
