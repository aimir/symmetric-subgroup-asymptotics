import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementGLDivisibility
import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor
import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput

/-! A finite arithmetic certificate for actual primitive-affine ordinary
generators. The only group estimate uses the original complement's faithful
linear representation. The selected ternary plane is a checked pilot,
not a primitive-group census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineCoarsePrimeMultiplicity

def linearBudget (p d : ℕ) : ℕ :=
  ArithmeticFunction.cardFactors (fullLinearOrder p d) + 1

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P

theorem genRank_le_linearBudget
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive) :
    MarkedC4.genRank G ≤ linearBudget P.p C.d := by
  let x : X := Classical.arbitrary X
  letI : Fact P.p.Prime := C.primeFact
  have hdvd := P.complement_card_dvd_GL_order hprimitive C x
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin C.d) (ZMod P.p)) =
      fullLinearOrder P.p C.d := by
    simpa only [fullLinearOrder, Fintype.card_eq_nat_card, Nat.card_zmod] using
      (Matrix.card_GL_field (𝔽 := ZMod P.p) C.d)
  have hne : fullLinearOrder P.p C.d ≠ 0 := by rw [← hGL]; exact Nat.card_pos.ne'
  have hc := FiniteGroupPrimeMultiplicityGenerators.cardFactors_mono_of_dvd
    (Nat.card_pos (α := P.complement x)).ne' hne hdvd
  exact (P.genRank_le_complement_add_one hprimitive x).trans
    (Nat.add_le_add_right
      ((FiniteGroupPrimeMultiplicityGenerators.genRank_le_cardFactors
        (P.complement x)).trans hc) 1)

theorem genRank_le_ceiling_of_arithmetic
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (D u : ℕ) (hD : 0 < D) (hpow : (P.p ^ C.d) ^ D ≤ 2 ^ u)
    (hsquare : (linearBudget P.p C.d - 1) ^ 2 * u < D * (P.p ^ C.d) ^ 2) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  let x : X := Classical.arbitrary X
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hn : Nat.card X = P.p ^ C.d := by
    simpa only [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv x
  have h := IntegerLogSquareRootCeilingCertificate.le_ceil_of_square
    (P.p ^ C.d) D u (linearBudget P.p C.d)
    (by rw [← hn]; exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
    hD (by unfold linearBudget; omega) hpow hsquare
  rw [← hn] at h
  exact (genRank_le_linearBudget P hprimitive C).trans h

theorem genRank_le_ceiling_of_ternary_plane
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (hp : P.p = 3) (hd : C.d = 2) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  apply genRank_le_ceiling_of_arithmetic P hprimitive C 16 51 (by decide)
  · rw [hp, hd]
    decide +kernel
  · rw [hp, hd]
    decide +kernel

theorem genRank_le_ceiling_of_binary_nine
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (hp : P.p = 2) (hd : C.d = 9) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  apply genRank_le_ceiling_of_arithmetic P hprimitive C 16 144 (by decide)
  · rw [hp, hd]
    decide +kernel
  · rw [hp, hd]
    decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineCoarsePrimeMultiplicity
