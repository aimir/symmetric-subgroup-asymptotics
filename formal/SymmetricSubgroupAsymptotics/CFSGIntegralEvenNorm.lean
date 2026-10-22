import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPairing
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Even integral norms for an actual symmetric matrix with even diagonal.
This is a lattice calculation, independent of a root-system recognition theorem. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGIntegralEvenNorm

variable {V : Type*} [AddCommGroup V]

theorem even_norm_add (B : LinearMap.BilinForm ℤ V)
    (hs : ∀ x y, B x y=B y x) (x y : V)
    (hx : Even (B x x)) (hy : Even (B y y)) : Even (B (x+y) (x+y)) := by
  rcases hx with ⟨a,ha⟩
  rcases hy with ⟨b,hb⟩
  refine ⟨a+b+B x y,?_⟩
  simp only [map_add,LinearMap.add_apply,hs y x]
  rw [ha,hb]
  ring

theorem even_norm_sum {ι : Type*} (B : LinearMap.BilinForm ℤ V)
    (hs : ∀ x y, B x y=B y x) (s : Finset ι) (v : ι→V)
    (hv : ∀ i∈s, Even (B (v i) (v i))) :
    Even (B (∑ i∈s,v i) (∑ i∈s,v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact even_norm_add B hs _ _ (hv i (Finset.mem_insert_self i s))
        (ih (fun j hj=>hv j (Finset.mem_insert_of_mem hj)))

open CFSGIntegerMatrixPairing
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem matrix_norm_even (A : Matrix n n ℤ) (hs : A.transpose=A)
    (hd : ∀ i,Even (A i i)) (x : n→ℤ) : Even (integerPairing A x x) := by
  have he := pi_eq_sum_univ' x
  rw [he]
  apply even_norm_sum (integerPairing A) (integer_symmetric A hs)
  intro i _
  simpa only [LinearMap.BilinForm.smul_left,LinearMap.BilinForm.smul_right,
    integerPairing,Matrix.toBilin'_single,smul_eq_mul] using
    ((hd i).mul_left (x i)).mul_left (x i)

theorem positive_even_norm_ge_two (A : Matrix n n ℤ) (hs : A.transpose=A)
    (hp : (rationalMatrix A).PosDef) (hd : ∀ i,Even (A i i))
    (x : n→ℤ) (hx : x ≠ 0) : 2 ≤ integerPairing A x x := by
  have hcx : castVector x≠0 := by
    intro h
    apply hx
    apply castVector_injective
    simpa [castVector] using h
  have hpos : (0:ℚ)<(integerPairing A x x:ℚ) := by
    rw [←cast_pairing]
    simpa only [rationalPairing,Matrix.toBilin'_apply',star_trivial] using
      hp.dotProduct_mulVec_pos hcx
  have hz : (0:ℤ) < integerPairing A x x := by exact_mod_cast hpos
  rcases matrix_norm_even A hs hd x with ⟨a,ha⟩
  omega

end SymmetricSubgroupAsymptotics.CFSGIntegralEvenNorm
