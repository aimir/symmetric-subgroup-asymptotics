import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadical

/-! Actual Gaussian-clearing parameters for a signed-Hermitian
hyperbolic column. Isotropy proves the precise radical central equation;
no trace-solvability choice, full-unitary recognition, or generation
premise is supplied. All identities include characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryColumnClearing
open CFSGTwistedAUnitaryParameters CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [Field K] [Fintype J] [DecidableEq J]

theorem hermitianNorm_smul (sigma : K ≃+* K) (H : Matrix J J K)
    (c : K) (z : J → K) :
    hermitianNorm sigma H (c • z) = sigma c * c * hermitianNorm sigma H z := by
  have hc : (fun i => sigma ((c • z) i)) = sigma c • (fun i => sigma (z i)) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  change dotProduct (fun i => sigma ((c • z) i)) (H *ᵥ (c • z)) = _
  rw [hc, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  change sigma c * (c * hermitianNorm sigma H z) = _
  ring

theorem radicalRow_dotProduct (sigma : K ≃+* K) (eps : K) (H : Matrix J J K)
    (v z : J → K) :
    dotProduct (radicalRow sigma eps H v) z =
      -eps * dotProduct (sigma ∘ v) (H *ᵥ z) := by
  change dotProduct ((-eps) • ((sigma ∘ v) ᵥ* H)) z = _
  rw [smul_dotProduct, ← Matrix.dotProduct_mulVec]
  rfl

def clearVector (b : K) (z : J → K) : J → K := (-b⁻¹) • z

def clearCentral (sigma : K ≃+* K) (eps a b : K) : K := eps * sigma a / sigma b

theorem sigma_clearVector (sigma : K ≃+* K) (b : K) (z : J → K) :
    sigma ∘ clearVector b z = (-(sigma b)⁻¹) • (sigma ∘ z) := by
  funext i
  simp only [clearVector, Function.comp_apply, Pi.smul_apply, smul_eq_mul,
    map_mul, map_neg, map_inv₀]

theorem clearVector_norm (sigma : K ≃+* K) (H : Matrix J J K)
    (b : K) (z : J → K) :
    hermitianNorm sigma H (clearVector b z) =
      hermitianNorm sigma H z / (sigma b * b) := by
  rw [clearVector, hermitianNorm_smul, map_neg, map_inv₀]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem clearVector_row_dot (sigma : K ≃+* K) (eps : K) (H : Matrix J J K)
    (b : K) (z : J → K) :
    dotProduct (radicalRow sigma eps H (clearVector b z)) z =
      eps * hermitianNorm sigma H z / sigma b := by
  rw [radicalRow_dotProduct, sigma_clearVector, smul_dotProduct]
  change (-eps) * ((-(sigma b)⁻¹) * hermitianNorm sigma H z) = _
  simp only [div_eq_mul_inv]
  ring

theorem clearing_central_condition (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x)
    (eps : K) (heps : eps = 1 ∨ eps = -1) (H : Matrix J J K)
    (a b : K) (z : J → K) (hb : b ≠ 0)
    (hiso : sigma a * b + hermitianNorm sigma H z + eps * sigma b * a = 0) :
    sigma (clearCentral sigma eps a b) + eps * clearCentral sigma eps a b =
      -hermitianNorm sigma H (clearVector b z) := by
  have hse : sigma eps = eps := by rcases heps with rfl | rfl <;> simp
  have he2 : eps * eps = 1 := by rcases heps with rfl | rfl <;> ring
  have hsb : sigma b ≠ 0 := (map_ne_zero sigma).mpr hb
  have hsc : sigma (clearCentral sigma eps a b) = eps * a / b := by
    rw [clearCentral, map_div₀, map_mul, hse, hsigma, hsigma]
  have hec : eps * clearCentral sigma eps a b = sigma a / sigma b := by
    calc
      _ = (eps * eps) * (sigma a / sigma b) := by unfold clearCentral; ring
      _ = _ := by rw [he2, one_mul]
  have hnum : eps * a * sigma b + sigma a * b = -hermitianNorm sigma H z := by
    calc
      _ = (sigma a * b + hermitianNorm sigma H z + eps * sigma b * a) -
          hermitianNorm sigma H z := by ring
      _ = _ := by rw [hiso]; ring
  calc
    _ = (eps * a * sigma b + sigma a * b) / (b * sigma b) := by
      rw [hsc, hec]
      field_simp [hb, hsb] <;> ring
    _ = -hermitianNorm sigma H z / (b * sigma b) := by rw [hnum]
    _ = _ := by rw [clearVector_norm]; simp only [mul_comm b (sigma b), neg_div]

theorem clearing_head_zero (sigma : K ≃+* K) (eps : K)
    (heps : eps = 1 ∨ eps = -1) (H : Matrix J J K)
    (a b : K) (z : J → K) (hb : b ≠ 0)
    (hiso : sigma a * b + hermitianNorm sigma H z + eps * sigma b * a = 0) :
    a + dotProduct (radicalRow sigma eps H (clearVector b z)) z +
      clearCentral sigma eps a b * b = 0 := by
  have he2 : eps * eps = 1 := by rcases heps with rfl | rfl <;> ring
  have hsb : sigma b ≠ 0 := (map_ne_zero sigma).mpr hb
  rw [clearVector_row_dot]
  calc
    _ = (eps * eps) * a + eps * hermitianNorm sigma H z / sigma b +
        clearCentral sigma eps a b * b := by rw [he2, one_mul]
    _ = eps * (sigma a * b + hermitianNorm sigma H z + eps * sigma b * a) / sigma b := by
      unfold clearCentral
      field_simp [hsb] <;> ring
    _ = 0 := by rw [hiso]; simp

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryColumnClearing
