import SymmetricSubgroupAsymptotics.BinaryFourSubgroupOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementGLDivisibility
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! The literal degree-sixteen primitive-affine ordinary-generator bound.
The original point stabilizer embeds faithfully in binary GL4. No finite
primitive catalogue, global permutation bound, or classification input occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenOrdinaryGenerators

private theorem complement_rank_bound {H : Type} [Group H] [Finite H]
    (p d : ℕ) [Fact p.Prime] (hp : p = 2) (hd : d = 4)
    (f : H →* Matrix.GeneralLinearGroup (Fin d) (ZMod p))
    (hf : Function.Injective f) : MarkedC4.genRank H ≤ 7 := by
  subst p
  subst d
  exact BinaryFourSubgroupOrdinaryGenerators.genRank_le_seven_of_injective f hf

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P

theorem genRank_le_eight (hprimitive : MulAction.IsPreprimitive G X)
    (hdegree : Nat.card X = 16) : MarkedC4.genRank G ≤ 8 := by
  let C := P.elementaryChart hprimitive
  let x : X := Classical.arbitrary X
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hpow : P.p ^ C.d = 16 := by
    have he := P.degree_eq_prime_pow_finrank C.equiv x
    simpa only [PrimitiveAffineProfile.ElementaryChart.d,hdegree] using he.symm
  have hpdiv : P.p ∣ 2 ^ 4 := by
    change P.p ∣ 16
    rw [←hpow]
    exact dvd_pow_self _ C.d_pos.ne'
  have hp : P.p = 2 := Nat.prime_eq_prime_of_dvd_pow P.p_prime (by decide) hpdiv
  have hd : C.d = 4 := Nat.pow_right_injective (by decide : 2 ≤ 2)
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
    (hdegree : Nat.card X = 16) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hnum := IntegerLogSquareRootCeilingCertificate.le_ceil_of_square
    16 1 4 8 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hdegree]
  exact (genRank_le_eight P hprimitive hdegree).trans hnum

theorem exists_generating_finset (hprimitive : MulAction.IsPreprimitive G X)
    (hdegree : Nat.card X = 16) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ S.card ≤ 8 := by
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hgen,hcard.le.trans (genRank_le_eight P hprimitive hdegree)⟩

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenOrdinaryGenerators
