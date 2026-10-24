import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementGLDivisibility
import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeLineCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDimensionOrder
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.BigOperators.Fin

/-! Literal small affine orders, through the original translation subgroup
and its faithful complement representation. The prime-degree statement
uses the actual prime-line embedding; degree nine uses the actual
positive translation dimension. No finite group catalogue is invoked. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSmallLocalOrderDivisibility

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

theorem card_dvd_degree_mul_GL
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive) (x : X) :
    Nat.card G ∣ Nat.card X *
      Nat.card (Matrix.GeneralLinearGroup (Fin C.d) (ZMod P.p)) := by
  have horder : Nat.card G = Nat.card X * Nat.card (P.complement x) := by
    rw [←P.card_eq x]
    exact (P.isComplement'_complement x).card_mul.symm
  rw [horder]
  exact Nat.mul_dvd_mul_left _ (P.complement_card_dvd_matrix_GL hprimitive C x)

omit [Nontrivial X] in
include P in
theorem card_dvd_prime_mul_pred (p : ℕ) [Fact p.Prime] (x : X)
    (hdegree : Nat.card X = p) : Nat.card G ∣ p*(p-1) := by
  have hdiv := Subgroup.card_dvd_of_injective
    (PrimitiveAffinePrimeLineCoordinates.coordinates p P x hdegree)
    (PrimitiveAffinePrimeLineCoordinates.coordinates_injective p P x hdegree)
  have hline : Nat.card (ScalarAffineLineGroup.Line (ZMod p)) = p*(p-1) := by
    rw [SemidirectProduct.card,Nat.card_units,Nat.card_zmod]
    have hm : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
    rw [hm]
  exact hline ▸ hdiv

include P in
theorem card_dvd_twenty (x : X) (hdegree : Nat.card X = 5) : Nat.card G ∣ 20 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  simpa using card_dvd_prime_mul_pred P 5 x hdegree

include P in
theorem card_dvd_forty_two (x : X) (hdegree : Nat.card X = 7) : Nat.card G ∣ 42 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  simpa using card_dvd_prime_mul_pred P 7 x hdegree

include P in
theorem card_dvd_four_hundred_thirty_two
    (hprimitive : MulAction.IsPreprimitive G X) (x : X)
    (hdegree : Nat.card X = 9) : Nat.card G ∣ 432 := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hpower : P.p^C.d = 3^2 := by
    simpa only [PrimitiveAffineProfile.ElementaryChart.d,hdegree] using
      (P.degree_eq_prime_pow_finrank C.equiv x).symm
  obtain ⟨hp,hd⟩ := Nat.Prime.pow_inj' P.p_prime (by decide : Nat.Prime 3)
    (by have hh := C.d_pos; omega) (by decide : (2 : ℕ) ≠ 0) hpower
  have hh := card_dvd_degree_mul_GL P hprimitive C x
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 48 := by
    have he : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) =
        ∏ i : Fin 2, (3^2-3^(i : ℕ)) := by
      simpa only [Fintype.card_eq_nat_card,Nat.card_zmod] using
        (Matrix.card_GL_field (𝔽 := ZMod 3) 2)
    rw [he]
    decide +kernel
  rw [hdegree,hp,hd,hGL] at hh
  exact hh

end SymmetricSubgroupAsymptotics.PrimitiveAffineSmallLocalOrderDivisibility
