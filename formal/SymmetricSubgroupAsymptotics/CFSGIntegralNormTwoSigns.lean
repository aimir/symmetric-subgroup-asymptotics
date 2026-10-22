import SymmetricSubgroupAsymptotics.CFSGIntegralEvenNorm
import Mathlib.Tactic.Positivity

/-! The actual sign property for a positive-definite integral Cartan lattice.
Off-diagonal nonpositivity and even norms exclude roots with both signs. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGIntegralNormTwoSigns
open CFSGIntegerMatrixPairing CFSGIntegralEvenNorm
variable {n : Type*} [Fintype n] [DecidableEq n]

def positivePart (x : n→ℤ) : n→ℤ := fun i=>max (x i) 0
def negativePart (x : n→ℤ) : n→ℤ := fun i=>max (-x i) 0

theorem parts_sub (x : n→ℤ) : positivePart x-negativePart x=x := by
  ext i
  simp only [positivePart,negativePart,Pi.sub_apply]
  omega

theorem cross_nonpositive (A : Matrix n n ℤ)
    (ho : ∀ i j,i≠j→A i j≤0) (x : n→ℤ) :
    integerPairing A (positivePart x) (negativePart x)≤0 := by
  simp only [integerPairing,Matrix.toBilin'_apply]
  apply Finset.sum_nonpos
  intro i _
  apply Finset.sum_nonpos
  intro j _
  by_cases hij : i=j
  · subst j
    have he : positivePart x i*negativePart x i=0 := by
      simp only [positivePart,negativePart]
      rcases le_total (x i) 0 with h|h <;> simp [max_eq_left,max_eq_right,h]
    calc
      positivePart x i*A i i*negativePart x i=
          (positivePart x i*negativePart x i)*A i i := by ring
      _ =0 := by rw [he,zero_mul]
      _ ≤0 := le_rfl
  · exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (le_max_right _ _) (ho i j hij))
      (le_max_right _ _)

theorem norm_two_coordinates_one_sign (A : Matrix n n ℤ) (hs : A.transpose=A)
    (hp : (rationalMatrix A).PosDef) (hd : ∀ i,Even (A i i))
    (ho : ∀ i j,i≠j→A i j≤0) (x : n→ℤ)
    (hx : integerPairing A x x=2) : (∀ i,0≤x i) ∨ (∀ i,x i≤0) := by
  by_cases hplus : positivePart x=0
  · right
    intro i
    have hi := congrFun hplus i
    change max (x i) 0=0 at hi
    omega
  by_cases hminus : negativePart x=0
  · left
    intro i
    have hi := congrFun hminus i
    change max (-x i) 0=0 at hi
    omega
  have hpos := positive_even_norm_ge_two A hs hp hd (positivePart x) hplus
  have hneg := positive_even_norm_ge_two A hs hp hd (negativePart x) hminus
  have hcross := cross_nonpositive A ho x
  have he : integerPairing A x x=
      integerPairing A (positivePart x) (positivePart x)+
      integerPairing A (negativePart x) (negativePart x)-
      2*integerPairing A (positivePart x) (negativePart x) := by
    conv_lhs => rw [←parts_sub x]
    simp only [map_sub,LinearMap.sub_apply,
      integer_symmetric A hs (negativePart x) (positivePart x)]
    ring
  omega

end SymmetricSubgroupAsymptotics.CFSGIntegralNormTwoSigns
