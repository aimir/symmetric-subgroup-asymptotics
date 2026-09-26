import SymmetricSubgroupAsymptotics.BinaryCarrierConeA
import SymmetricSubgroupAsymptotics.BinaryCarrierConeB

/-! Universal real inequalities for both carrier cones. The two square
certificates discharge every matrix positivity claim. The final split is
exhaustive on the entire original rectangle, including j < ell. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryCarrierCone

private theorem sum6_scalar (f : Fin 6 → ℝ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (0)))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5
  ring

private theorem pairMatrix64_row0 (z : Fin 6 → ℝ) :
    (∑ j, pairMatrix64 0 j * z 0 * z j) =
      (5)*z 0*z 0 + (6)*z 0*z 1 + (34)*z 0*z 2 + (28)*z 0*z 3 + (32)*z 0*z 4 + (30)*z 0*z 5 := by
  rw [sum6_scalar] <;> rfl

private theorem pairMatrix64_row1 (z : Fin 6 → ℝ) :
    (∑ j, pairMatrix64 1 j * z 1 * z j) =
      (6)*z 1*z 0 + (0)*z 1*z 1 + (44)*z 1*z 2 + (36)*z 1*z 3 + (40)*z 1*z 4 + (36)*z 1*z 5 := by
  rw [sum6_scalar] <;> rfl

private theorem pairMatrix64_row2 (z : Fin 6 → ℝ) :
    (∑ j, pairMatrix64 2 j * z 2 * z j) =
      (34)*z 2*z 0 + (44)*z 2*z 1 + (0)*z 2*z 2 + (16)*z 2*z 3 + (20)*z 2*z 4 + (40)*z 2*z 5 := by
  rw [sum6_scalar] <;> rfl

private theorem pairMatrix64_row3 (z : Fin 6 → ℝ) :
    (∑ j, pairMatrix64 3 j * z 3 * z j) =
      (28)*z 3*z 0 + (36)*z 3*z 1 + (16)*z 3*z 2 + (12)*z 3*z 3 + (16)*z 3*z 4 + (32)*z 3*z 5 := by
  rw [sum6_scalar] <;> rfl

private theorem pairMatrix64_row4 (z : Fin 6 → ℝ) :
    (∑ j, pairMatrix64 4 j * z 4 * z j) =
      (32)*z 4*z 0 + (40)*z 4*z 1 + (20)*z 4*z 2 + (16)*z 4*z 3 + (16)*z 4*z 4 + (32)*z 4*z 5 := by
  rw [sum6_scalar] <;> rfl

private theorem pairMatrix64_row5 (z : Fin 6 → ℝ) :
    (∑ j, pairMatrix64 5 j * z 5 * z j) =
      (30)*z 5*z 0 + (36)*z 5*z 1 + (40)*z 5*z 2 + (32)*z 5*z 3 + (32)*z 5*z 4 + (24)*z 5*z 5 := by
  rw [sum6_scalar] <;> rfl

private theorem pairMatrix64_expansion (z : Fin 6 → ℝ) :
    quadratic pairMatrix64 z =
      ((5)*z 0*z 0 + (6)*z 0*z 1 + (34)*z 0*z 2 + (28)*z 0*z 3 + (32)*z 0*z 4 + (30)*z 0*z 5) +
      ((6)*z 1*z 0 + (0)*z 1*z 1 + (44)*z 1*z 2 + (36)*z 1*z 3 + (40)*z 1*z 4 + (36)*z 1*z 5) +
      ((34)*z 2*z 0 + (44)*z 2*z 1 + (0)*z 2*z 2 + (16)*z 2*z 3 + (20)*z 2*z 4 + (40)*z 2*z 5) +
      ((28)*z 3*z 0 + (36)*z 3*z 1 + (16)*z 3*z 2 + (12)*z 3*z 3 + (16)*z 3*z 4 + (32)*z 3*z 5) +
      ((32)*z 4*z 0 + (40)*z 4*z 1 + (20)*z 4*z 2 + (16)*z 4*z 3 + (16)*z 4*z 4 + (32)*z 4*z 5) +
      ((30)*z 5*z 0 + (36)*z 5*z 1 + (40)*z 5*z 2 + (32)*z 5*z 3 + (32)*z 5*z 4 + (24)*z 5*z 5) := by
  unfold quadratic
  rw [sum6_scalar]
  rw [pairMatrix64_row0, pairMatrix64_row1, pairMatrix64_row2, pairMatrix64_row3, pairMatrix64_row4, pairMatrix64_row5]

private theorem mass_expansion (p : Fin 6 → ℝ) :
    mass p = p 0 + p 1 + p 2 + p 3 + p 4 + p 5 := by
  exact sum6_scalar p

private theorem marks_expansion (j ell : ℝ) (p : Fin 6 → ℝ) :
    (∑ i, p i * (ell*(alpha i+beta i) + alpha i*max (j-2*ell) 0)) =
      p 0*(ell*(5/8+3/8)+(5/8)*max (j-2*ell) 0) +
      p 1*(ell*(3/4+1/2)+(3/4)*max (j-2*ell) 0) +
      p 2*(ell*(0+0)+0*max (j-2*ell) 0) +
      p 3*(ell*(1/4+1/4)+(1/4)*max (j-2*ell) 0) +
      p 4*(ell*(1/4+1/4)+(1/4)*max (j-2*ell) 0) +
      p 5*(ell*(1/2+1/2)+(1/2)*max (j-2*ell) 0) := by
  rw [sum6_scalar] <;> rfl

/-- First cone: nonnegative coordinates are (ell, j-2ell, R-j). -/
theorem energy_le_of_two_mul_le (R j ell : ℝ) (p : Fin 6 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hell : 0 ≤ ell) (hcone : 2*ell ≤ j) (hj : j ≤ R) :
    energy R j ell p ≤ benchmark R p := by
  let z : Fin 9 → ℝ := ![p 0,p 1,p 2,p 3,p 4,p 5,ell,j-2*ell,R-j]
  have hz : ∀ i, 0 ≤ z i := by
    intro i
    fin_cases i <;> norm_num [z] <;> first | exact hp _ | linarith
  have hmax : max (j-2*ell) 0 = j-2*ell := max_eq_left (by linarith)
  have hid : quadratic matrixA z = 5248*(benchmark R p-energy R j ell p) := by
    have h0 : z 0 = p 0 := rfl
    have h1 : z 1 = p 1 := rfl
    have h2 : z 2 = p 2 := rfl
    have h3 : z 3 = p 3 := rfl
    have h4 : z 4 = p 4 := rfl
    have h5 : z 5 = p 5 := rfl
    have h6 : z 6 = ell := rfl
    have h7 : z 7 = j-2*ell := rfl
    have h8 : z 8 = R-j := rfl
    rw [matrixA_expansion]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, benchmark, energy,
      pairMatrix64_expansion, mass_expansion]
    rw [marks_expansion, hmax]
    ring
  have h := matrixA_nonneg z hz
  rw [hid] at h
  linarith

/-- Second cone: (j, 2ell-j, R-2ell) stays nonnegative even when j < ell. -/
theorem energy_le_of_le_two_mul (R j ell : ℝ) (p : Fin 6 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hj : 0 ≤ j) (hcone : j ≤ 2*ell) (hell : 2*ell ≤ R) :
    energy R j ell p ≤ benchmark R p := by
  let z : Fin 9 → ℝ := ![p 0,p 1,p 2,p 3,p 4,p 5,j,2*ell-j,R-2*ell]
  have hz : ∀ i, 0 ≤ z i := by
    intro i
    fin_cases i <;> norm_num [z] <;> first | exact hp _ | linarith
  have hmax : max (j-2*ell) 0 = 0 := max_eq_right (by linarith)
  have hid : quadratic matrixB z = 5248*(benchmark R p-energy R j ell p) := by
    have h0 : z 0 = p 0 := rfl
    have h1 : z 1 = p 1 := rfl
    have h2 : z 2 = p 2 := rfl
    have h3 : z 3 = p 3 := rfl
    have h4 : z 4 = p 4 := rfl
    have h5 : z 5 = p 5 := rfl
    have h6 : z 6 = j := rfl
    have h7 : z 7 = 2*ell-j := rfl
    have h8 : z 8 = R-2*ell := rfl
    rw [matrixB_expansion]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, benchmark, energy,
      pairMatrix64_expansion, mass_expansion]
    rw [marks_expansion, hmax]
    ring
  have h := matrixB_nonneg z hz
  rw [hid] at h
  linarith

/-- The complete rational carrier-cone inequality for arbitrary real masses.
Only the original domain inequalities are inputs; no PSD, cone membership,
group-profile certificate, or numerical majorant is assumed. -/
theorem energy_le (R j ell : ℝ) (p : Fin 6 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R/2) :
    energy R j ell p ≤ R^2/4 + (139/328)*R*(∑ i, p i) +
      (627/2624)*(∑ i, p i)^2 := by
  change energy R j ell p ≤ benchmark R p
  by_cases hcone : 2*ell ≤ j
  · exact energy_le_of_two_mul_le R j ell p hp hell.1 hcone hj.2
  · exact energy_le_of_le_two_mul R j ell p hp hj.1 (by linarith) (by linarith [hell.2])

/-- The physical mass substitution gives the exact reserve used by the
carrier mixture. The equality of masses is explicit; no group-profile
identification or counting estimate is inferred from this real inequality. -/
theorem energy_le_reserve (R T j ell : ℝ) (p : Fin 6 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hj : 0 ≤ j ∧ j ≤ R)
    (hell : 0 ≤ ell ∧ ell ≤ R/2) (hmass : ∑ i, p i = 4*T) :
    energy R j ell p ≤ (R+4*T)^2/4 - (25/82)*R*T - (29/164)*T^2 := by
  have h := energy_le R j ell p hp hj hell
  rw [hmass] at h
  calc
    _ ≤ R^2/4 + (139/328)*R*(4*T) + (627/2624)*(4*T)^2 := h
    _ = _ := by ring

end SymmetricSubgroupAsymptotics.BinaryCarrierCone
