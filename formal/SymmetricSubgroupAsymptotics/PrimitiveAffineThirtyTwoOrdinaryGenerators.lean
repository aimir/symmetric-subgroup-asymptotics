import SymmetricSubgroupAsymptotics.BinaryFiveLinearOrderFour
import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGeneratorSaving
import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor
import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementGLDivisibility
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! The literal degree-thirty-two primitive-affine ordinary-generator bound.
The original point stabilizer embeds faithfully in binary GL5. No finite
primitive catalogue, global permutation bound, or classification input occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineThirtyTwoOrdinaryGenerators

private theorem complement_rank_bound {H : Type} [Group H] [Finite H]
    (p d : ℕ) [Fact p.Prime] (hp : p=2) (hd : d=5)
    (f : H →* Matrix.GeneralLinearGroup (Fin d) (ZMod p))
    (hf : Function.Injective f) : MarkedC4.genRank H + 1 ≤ 15 := by
  subst p
  subst d
  have hc := FiniteGroupPrimeMultiplicityGeneratorSaving.genRank_add_one_le_of_injective_into_order_four
    f hf BinaryFiveLinearOrderFour.element BinaryFiveLinearOrderFour.order_four
  have ho : ArithmeticFunction.cardFactors
      (Nat.card BinaryFiveLinearOrderFour.General) = 15 := by
    have he : Nat.card BinaryFiveLinearOrderFour.General = fullLinearOrder 2 5 := by
      rw [Matrix.card_GL_field]
      simp only [ZMod.card]
    rw [he]
    decide +kernel
  exact ho ▸ hc

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P

theorem genRank_le_fifteen (hprimitive : MulAction.IsPreprimitive G X)
    (hdegree : Nat.card X = 32) : MarkedC4.genRank G ≤ 15 := by
  let C := P.elementaryChart hprimitive
  let x : X := Classical.arbitrary X
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hpow : P.p ^ C.d = 32 := by
    have he := P.degree_eq_prime_pow_finrank C.equiv x
    simpa only [PrimitiveAffineProfile.ElementaryChart.d,hdegree] using he.symm
  have hpdiv : P.p ∣ 2 ^ 5 := by
    change P.p ∣ 32
    rw [←hpow]
    exact dvd_pow_self _ C.d_pos.ne'
  have hp : P.p = 2 := Nat.prime_eq_prime_of_dvd_pow P.p_prime (by decide) hpdiv
  have hd : C.d = 5 := Nat.pow_right_injective (by decide : 2 ≤ 2)
    (by simpa only [hp] using hpow)
  let f0 : P.complement x →* Matrix.GeneralLinearGroup (Fin C.d) (ZMod P.p) :=
    FaithfulFiniteLinearRepresentationOrder.matrixHom
      (P.complementRepresentationCore hprimitive C x).ρ
  have hf0 : Function.Injective f0 :=
    FaithfulFiniteLinearRepresentationOrder.matrixHom_injective _
      (P.complementRepresentationCore_injective hprimitive C x)
  have hc := complement_rank_bound P.p C.d hp hd f0 hf0
  exact (P.genRank_le_complement_add_one hprimitive x).trans (by omega)

theorem genRank_le_ceiling (hprimitive : MulAction.IsPreprimitive G X)
    (hdegree : Nat.card X = 32) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hnum := IntegerLogSquareRootCeilingCertificate.le_ceil_of_square
    32 1 5 15 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hdegree]
  exact (genRank_le_fifteen P hprimitive hdegree).trans hnum

theorem exists_generating_finset (hprimitive : MulAction.IsPreprimitive G X)
    (hdegree : Nat.card X = 32) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ S.card ≤ 15 := by
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,hcard.le.trans (genRank_le_fifteen P hprimitive hdegree)⟩

end SymmetricSubgroupAsymptotics.PrimitiveAffineThirtyTwoOrdinaryGenerators
