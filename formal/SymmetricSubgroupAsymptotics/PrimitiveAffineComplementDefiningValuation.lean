import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementGLDivisibility
import SymmetricSubgroupAsymptotics.PrimeGeneralLinearDefiningValuation
import SymmetricSubgroupAsymptotics.PrimitiveAffineDimensionOrder

/-! Automatic defining-prime valuations of actual primitive affine
groups. Faithful complement divisibility gives at most d(d-1)/2; the
literal regular translation subgroup adds exactly d. No scalar target
bound or complement catalogue is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

theorem complement_defining_valuation_le
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive) (x : X) :
    (Nat.card (P.complement x)).factorization P.p ≤ C.d * (C.d - 1) / 2 := by
  letI : Fact P.p.Prime := C.primeFact
  have hd := P.complement_card_dvd_matrix_GL hprimitive C x
  have hh := (Nat.factorization_le_iff_dvd
    (Nat.card_pos (α := P.complement x)).ne'
    (Nat.card_pos (α := Matrix.GeneralLinearGroup (Fin C.d) (ZMod P.p))).ne').mpr hd
  exact (hh P.p).trans_eq
    (PrimeGeneralLinearDefiningValuation.matrix_GL_defining_factorization P.p C.d P.p_prime)

theorem ambient_defining_valuation_le
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive) (x : X) :
    (Nat.card G).factorization P.p ≤ C.d * (C.d + 1) / 2 := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hx : Nat.card X = P.p ^ C.d := by
    simpa only [ElementaryChart.d] using P.degree_eq_prime_pow_finrank C.equiv x
  have hv : Nat.card P.V = P.p ^ C.d := (P.card_eq x).trans hx
  have hprod := (P.isComplement'_complement x).card_mul
  calc
    (Nat.card G).factorization P.p = C.d + (Nat.card (P.complement x)).factorization P.p := by
      rw [← hprod, hv, Nat.factorization_mul (pow_ne_zero _ P.p_prime.ne_zero)
        (Nat.card_pos (α := P.complement x)).ne', Finsupp.add_apply,
        Nat.factorization_pow_self P.p_prime]
    _ ≤ C.d + C.d * (C.d - 1) / 2 :=
      Nat.add_le_add_left (P.complement_defining_valuation_le hprimitive C x) _
    _ = C.d * (C.d + 1) / 2 := by
      have hs := Finset.sum_range_succ (fun i : ℕ => i) C.d
      calc
        C.d + C.d * (C.d - 1) / 2 = C.d * (C.d - 1) / 2 + C.d := Nat.add_comm _ _
        _ = (C.d + 1) * C.d / 2 := by
          simpa only [Finset.sum_range_id, Nat.add_sub_cancel] using hs.symm
        _ = C.d * (C.d + 1) / 2 := by rw [Nat.mul_comm (C.d + 1) C.d]

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
