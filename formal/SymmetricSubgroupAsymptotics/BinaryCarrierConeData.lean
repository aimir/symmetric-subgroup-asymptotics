import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Literal rational data for the two carrier cones. The pair matrix and
both marks retain their physical normalization. These are scalar numerical
objects; no group profile or carrier coverage is asserted here. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryCarrierCone

def quadratic {n : ℕ} (M : Fin n → Fin n → ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * z i * z j

theorem quadratic_nonneg {n : ℕ} (M : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hz : ∀ i, 0 ≤ z i) : 0 ≤ quadratic M z := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (hM i j) (hz i)) (hz j)

theorem quadratic_sub {n : ℕ} (M N : Fin n → Fin n → ℝ) (z : Fin n → ℝ) :
    quadratic (fun i j => M i j - N i j) z = quadratic M z - quadratic N z := by
  simp only [quadratic, sub_mul, Finset.sum_sub_distrib]

/-- The displayed pair matrix is 64 times the physically normalized matrix. -/
def pairMatrix64 : Fin 6 → Fin 6 → ℝ :=
  ![![5,6,34,28,32,30], ![6,0,44,36,40,36], ![34,44,0,16,20,40],
    ![28,36,16,12,16,32], ![32,40,20,16,16,32], ![30,36,40,32,32,24]]

def alpha : Fin 6 → ℝ := ![5/8,3/4,0,1/4,1/4,1/2]
def beta : Fin 6 → ℝ := ![3/8,1/2,0,1/4,1/4,1/2]
def mass (p : Fin 6 → ℝ) : ℝ := ∑ i, p i

/-- The complete scalar expression, including both marks and the positive part. -/
def energy (R j ell : ℝ) (p : Fin 6 → ℝ) : ℝ :=
  ell * (R/2-ell) + (j-ell)*(R-j) + quadratic pairMatrix64 p / 128 +
    ∑ i, p i * (ell*(alpha i+beta i) + alpha i*max (j-2*ell) 0)

def benchmark (R : ℝ) (p : Fin 6 → ℝ) : ℝ :=
  R^2/4 + (139/328)*R*mass p + (627/2624)*(mass p)^2

/-- Exact matrix for coordinates (p₁,...,p₆, ell, j-2ell, R-j). -/
def matrixA : Fin 9 → Fin 9 → ℝ :=
  ![![1049,1008,-140,106,-58,24,-400,-528,1112],
    ![1008,1254,-550,-222,-386,-222,-1056,-856,1112],
    ![-140,-550,1254,598,434,-386,2224,1112,1112],
    ![106,-222,598,762,598,-58,912,456,1112],
    ![-58,-386,434,598,598,-58,912,456,1112],
    ![24,-222,-386,-58,-58,270,-400,-200,1112],
    ![-400,-1056,2224,912,912,-400,5248,1312,-1312],
    ![-528,-856,1112,456,456,-200,1312,1312,-1312],
    ![1112,1112,1112,1112,1112,1112,-1312,-1312,1312]]

/-- Exact matrix for coordinates (p₁,...,p₆, j, 2ell-j, R-2ell). -/
def matrixB : Fin 9 → Fin 9 → ℝ :=
  ![![1049,1008,-140,106,-58,24,-200,-200,1112],
    ![1008,1254,-550,-222,-386,-222,-528,-528,1112],
    ![-140,-550,1254,598,434,-386,1112,1112,1112],
    ![106,-222,598,762,598,-58,456,456,1112],
    ![-58,-386,434,598,598,-58,456,456,1112],
    ![24,-222,-386,-58,-58,270,-200,-200,1112],
    ![-200,-528,1112,456,456,-200,1312,0,-656],
    ![-200,-528,1112,456,456,-200,0,3936,1968],
    ![1112,1112,1112,1112,1112,1112,-656,1968,1312]]

/-- The literal rational part supplied by the first certificate. -/
def psdA : Fin 9 → Fin 9 → ℝ :=
  ![![817,804,-548,-328,-393,-540/11,-896,-688,688],
    ![804,1254,-550,-288,-386,-222,-1129,-856,856],
    ![-548,-550,1254,423,434,-386,1836,1112,-1112],
    ![-328,-288,423,577,237,-3987/44,563,323,-323],
    ![-393,-386,434,237,490,-58,646,363,-363],
    ![-540/11,-222,-386,-3987/44,-58,270,-19363/44,-200,200],
    ![-896,-1129,1836,563,646,-19363/44,4645,1312,-1312],
    ![-688,-856,1112,323,363,-200,1312,1312,-1312],
    ![688,856,-1112,-323,-363,200,-1312,-1312,1312]]

/-- The literal rational part supplied by the second certificate. -/
def psdB : Fin 9 → Fin 9 → ℝ :=
  ![![729,721,-469,-236,-318,-602/11,-416,-480,86],
    ![721,1254,-550,-296,-386,-222,-565,-585,-2],
    ![-469,-550,1254,433,434,-386,917,950,-407],
    ![-236,-296,433,542,241,-4061/44,275,197,-56],
    ![-318,-386,434,241,469,-58,303,231,-65],
    ![-602/11,-222,-386,-4061/44,-58,270,-2413/11,-10005/44,8581/44],
    ![-416,-565,917,275,303,-2413/11,1254,-134,-813],
    ![-480,-585,950,197,231,-10005/44,-134,2690,591],
    ![86,-2,-407,-56,-65,8581/44,-813,591,891]]

end SymmetricSubgroupAsymptotics.BinaryCarrierCone
