import SymmetricSubgroupAsymptotics.CFSGTypeASLTwoWeyl
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.LinearCombination

/-! Two actual SL2 commutators whose commutator is nonscalar. The
parameter condition is square !=1, valid for an actual multiplicative
generator over every field of at least four elements. No simplicity
assumption is used in this matrix witness. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedASLTwoDerivedWitness
open Matrix CFSGTypeAElementaryMatrices CFSGTypeASLTwoWeyl
variable {K : Type} [Field K]

def delta (a : K) : SL2 (F := K) := ⁅upper a, lower (1 : K)⁆
def deltaArray (a : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1 + a + a ^ 2, -(a ^ 2); a, 1 - a]

theorem delta_val (a : K) : (delta a).val = deltaArray a := by
  simp only [delta, commutatorElement_def, upper, lower, elementary_inv]
  change Matrix.transvection (0 : Fin 2) 1 a * Matrix.transvection (1 : Fin 2) 0 1 *
    Matrix.transvection (0 : Fin 2) 1 (-a) * Matrix.transvection (1 : Fin 2) 0 (-1) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deltaArray, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply] <;> ring

def deltaUnit (a : K) : (Matrix (Fin 2) (Fin 2) K)ˣ :=
  Matrix.SpecialLinearGroup.toGL (delta a)

theorem deltaUnit_val (a : K) : (deltaUnit a : Matrix (Fin 2) (Fin 2) K) = deltaArray a :=
  delta_val a

theorem delta_commutator_not_scalar (a : K) (ha : a ≠ 0) (hsquare : a ^ 2 ≠ 1) :
    ¬ ∃ c : K, (↑(⁅deltaUnit (1 : K), deltaUnit a⁆) : Matrix (Fin 2) (Fin 2) K) =
      c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rintro ⟨c, hc⟩
  let u := deltaUnit (1 : K)
  let v := deltaUnit a
  have hcancel : ⁅u, v⁆ * (v * u) = u * v := by
    simp only [commutatorElement_def, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  have he := congrArg (fun w : (Matrix (Fin 2) (Fin 2) K)ˣ =>
    (w : Matrix (Fin 2) (Fin 2) K)) hcancel
  change (↑(⁅u, v⁆) : Matrix (Fin 2) (Fin 2) K) *
      ((v : Matrix (Fin 2) (Fin 2) K) * (u : Matrix (Fin 2) (Fin 2) K)) =
    (u : Matrix (Fin 2) (Fin 2) K) * (v : Matrix (Fin 2) (Fin 2) K) at he
  change (↑(⁅u, v⁆) : Matrix (Fin 2) (Fin 2) K) = c • 1 at hc
  rw [hc, smul_mul_assoc, one_mul] at he
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) he
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) he
  dsimp only [u, v] at h11 h10
  simp only [deltaUnit_val, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    deltaArray, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
    smul_eq_mul] at h11 h10
  have hca : c = a := by
    apply mul_right_cancel₀ ha
    linear_combination -h11
  rw [hca] at h10
  apply hsquare
  linear_combination h10

end SymmetricSubgroupAsymptotics.CFSGTwistedASLTwoDerivedWitness
