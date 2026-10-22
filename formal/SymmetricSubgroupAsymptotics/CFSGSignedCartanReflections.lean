import Mathlib.Data.Matrix.Cartan
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-! The original absolute-Cartan reflection matrices are conjugate to the
root-lattice reflection matrices by an explicit bipartite sign matrix.
This integral identity survives every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSignedCartanReflections
variable {I : Type*} [Fintype I] [DecidableEq I]

def cartanStep (A : Matrix I I ℤ) (i : I) : Matrix I I ℤ :=
  1-Matrix.of (fun j k=>if j=i then |A i k| else 0)

def latticeStep (A : Matrix I I ℤ) (i : I) : Matrix I I ℤ :=
  1-Matrix.of (fun j k=>if j=i then A k i else 0)

def cartanWord (A : Matrix I I ℤ) : List I→Matrix I I ℤ
  | []=>1
  | i::w=>cartanStep A i*cartanWord A w

def latticeWord (A : Matrix I I ℤ) : List I→Matrix I I ℤ
  | []=>1
  | i::w=>latticeStep A i*latticeWord A w

theorem signs_square (ε : I→ℤ) (hε : ∀i,ε i*ε i=1) :
    Matrix.diagonal ε*Matrix.diagonal ε=1 := by
  rw [Matrix.diagonal_mul_diagonal]
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j
    simp [hε]
  · simp [hij]

theorem step_intertwines (A : Matrix I I ℤ) (ε : I→ℤ)
    (hε : ∀i j,ε i*|A i j|=A j i*ε j) (i : I) :
    Matrix.diagonal ε*cartanStep A i=latticeStep A i*Matrix.diagonal ε := by
  apply Matrix.ext
  intro j k
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal]
  simp only [cartanStep,latticeStep,Matrix.sub_apply,Matrix.of_apply,Matrix.one_apply]
  by_cases hji : j=i
  · subst j
    simp only [if_true]
    by_cases hik : i=k
    · subst k
      simp only [if_true,mul_sub,sub_mul,mul_one,one_mul]
      rw [hε i i]
    · simp only [if_neg hik,if_true,mul_sub,sub_mul,mul_zero,zero_mul,zero_sub,mul_neg,neg_mul]
      exact congrArg Neg.neg (hε i k)
  · simp only [if_neg hji,sub_zero]
    by_cases hjk : j=k
    · subst k
      simp
    · simp [hjk]

theorem word_intertwines (A : Matrix I I ℤ) (ε : I→ℤ)
    (hε : ∀i j,ε i*|A i j|=A j i*ε j) (w : List I) :
    Matrix.diagonal ε*cartanWord A w=latticeWord A w*Matrix.diagonal ε := by
  induction w with
  | nil=>simp only [cartanWord,latticeWord,mul_one,one_mul]
  | cons i w ih=>
    rw [cartanWord,latticeWord,←mul_assoc,step_intertwines A ε hε,mul_assoc,ih,mul_assoc]

theorem cartanWord_eq_one_of_latticeWord_eq_one (A : Matrix I I ℤ) (ε : I→ℤ)
    (hε : ∀i,ε i*ε i=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (w : List I) (hw : latticeWord A w=1) : cartanWord A w=1 := by
  have hh := word_intertwines A ε hA w
  rw [hw,one_mul] at hh
  calc
    cartanWord A w=1*cartanWord A w := (one_mul _).symm
    _=(Matrix.diagonal ε*Matrix.diagonal ε)*cartanWord A w := by rw [signs_square ε hε]
    _=Matrix.diagonal ε*(Matrix.diagonal ε*cartanWord A w) := mul_assoc _ _ _
    _=Matrix.diagonal ε*Matrix.diagonal ε := congrArg (Matrix.diagonal ε*·) hh
    _=1 := signs_square ε hε

def E6Signs : Fin 6→ℤ := ![1,-1,-1,1,-1,1]
def E7Signs : Fin 7→ℤ := ![1,-1,-1,1,-1,1,-1]
def E8Signs : Fin 8→ℤ := ![1,-1,-1,1,-1,1,-1,1]

theorem E6_signs_square : ∀i,E6Signs i*E6Signs i=1 := by decide
theorem E7_signs_square : ∀i,E7Signs i*E7Signs i=1 := by decide
theorem E8_signs_square : ∀i,E8Signs i*E8Signs i=1 := by decide

theorem E6_signs_cartan : ∀i j,E6Signs i*|CartanMatrix.E₆ i j|=
    CartanMatrix.E₆ j i*E6Signs j := by decide
theorem E7_signs_cartan : ∀i j,E7Signs i*|CartanMatrix.E₇ i j|=
    CartanMatrix.E₇ j i*E7Signs j := by decide
theorem E8_signs_cartan : ∀i j,E8Signs i*|CartanMatrix.E₈ i j|=
    CartanMatrix.E₈ j i*E8Signs j := by decide

end SymmetricSubgroupAsymptotics.CFSGSignedCartanReflections
