import SymmetricSubgroupAsymptotics.CFSGPrimitiveBinaryFiveChiefBound
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTraceMargins
import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore

/-! The literal degree32 complement satisfies the prime-dimensional abelian
chief-length bound for every chosen actual chief series. No fixed-target
trace or canonical-series replacement occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private theorem chief_of_prime_eq_two_card_thirtyTwo
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    {p : ℕ} [Fact p.Prime] (hp : p = 2)
    {H W : Type} [Group H] [Finite H] [AddCommGroup W]
    [Module (ZMod p) W] [FiniteDimensional (ZMod p) W] [Finite W]
    (hW : Nat.card W = 32) (rho : Representation (ZMod p) H W)
    (hirr : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hns : ¬ IsSolvable H) (c : ActualChiefSeries H) :
    actualChiefSeriesAbelianLength c ≤ 4 := by
  subst p
  have hpow : 2 ^ Module.finrank (ZMod 2) W = 2 ^ 5 := by
    calc
      _ = Nat.card W := by
        simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)).symm
      _ = 2 ^ 5 := by norm_num [hW]
  exact CFSGPrimitiveBinaryFiveChiefBound.chief_abelianLength_le_four hindex rho hirr hf
    (Nat.pow_right_injective (by decide : 2 ≤ 2) hpow) hns c

namespace PrimitiveAffineProfile
open Non2UnipotentPrefixFiniteMenu

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem complementChief_abelianLength_le_four_of_degree32
    (P : PrimitiveAffineProfile G X)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hp : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hp)
    (x : X) (he : Nat.card X = 32)
    (c : ActualChiefSeries (P.complement x))
    (hn : ¬ IsSolvable (P.complement x)) : actualChiefSeriesAbelianLength c ≤ 4 := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hpower : P.p ^ C.d = 2 ^ 5 := by
    simpa only [he] using (P.degree_eq_prime_pow_finrank C.equiv x).symm
  have hp2 : P.p = 2 :=
    (prime_pow_positive_injective P.p_prime Nat.prime_two C.d_pos (by decide) hpower).1
  have hV : Nat.card C.V = 32 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod P.p), Nat.card_zmod]
    exact (P.degree_eq_prime_pow_finrank C.equiv x).symm.trans he
  exact chief_of_prime_eq_two_card_thirtyTwo hindex hp2 hV
    (P.complementRepresentationCore hp C x).ρ
    (P.complementRepresentation_irreducible hp C x)
    (P.complementRepresentationCore_injective hp C x) hn c

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics
