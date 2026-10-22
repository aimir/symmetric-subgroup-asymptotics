import SymmetricSubgroupAsymptotics.CFSGPrimitiveBinarySixTraceBound
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTraceMargins
import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore

/-! The literal degree64 complement has the proved six-dimensional trace
budget. Its original normal axes feed the existing nonsoluble source
constructor; no composition theorem or complement catalogue is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private theorem trace_of_prime_eq_two_card_sixtyFour
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    {p : ℕ} [Fact p.Prime] (hp : p = 2)
    {H W : Type} [Group H] [Finite H] [AddCommGroup W]
    [Module (ZMod p) W] [FiniteDimensional (ZMod p) W] [Finite W]
    (hW : Nat.card W = 64) (rho : Representation (ZMod p) H W)
    (hirr : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hns : ¬ IsSolvable H) (T : FixedTargetCompositionTrace H) :
    T.envelope.abelianLength ≤ 14 := by
  subst p
  have hpow : 2 ^ Module.finrank (ZMod 2) W = 2 ^ 6 := by
    calc
      _ = Nat.card W := by
        simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)).symm
      _ = 2 ^ 6 := by norm_num [hW]
  exact CFSGPrimitiveBinarySixTraceBound.trace_abelianLength_le_fourteen hindex rho hirr hf
    (Nat.pow_right_injective (by decide : 2 ≤ 2) hpow) hns T

namespace PrimitiveAffineProfile
open Non2UnipotentPrefixFiniteMenu

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem complementTrace_abelianLength_le_fourteen_of_degree64
    (P : PrimitiveAffineProfile G X)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hp : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hp)
    (x : X) (he : Nat.card X = 64)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hn : ¬ IsSolvable (P.complement x)) : T.envelope.abelianLength ≤ 14 := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hpower : P.p ^ C.d = 2 ^ 6 := by
    simpa only [he] using (P.degree_eq_prime_pow_finrank C.equiv x).symm
  have hp2 : P.p = 2 :=
    (prime_pow_positive_injective P.p_prime Nat.prime_two C.d_pos (by decide) hpower).1
  have hV : Nat.card C.V = 64 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod P.p), Nat.card_zmod]
    exact (P.degree_eq_prime_pow_finrank C.equiv x).symm.trans he
  exact trace_of_prime_eq_two_card_sixtyFour hindex hp2 hV
    (P.complementRepresentationCore hp C x).ρ
    (P.complementRepresentation_irreducible hp C x)
    (P.complementRepresentationCore_injective hp C x) hn T

theorem nonsoluble_margin_of_degree64_prime
    (P : PrimitiveAffineProfile G X)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hp : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hp)
    (x : X) (he : Nat.card X = 64)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hn : ¬ IsSolvable (P.complement x)) :
    preE7CharacterRho * 64 ≤ ((evenWidth 64 : ℝ) - 2) / 8 -
      (fixedTargetCompositionGamma * T.envelope.abelianLength + P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength (w := 64) (A := 14) T
    (P.complementTrace_abelianLength_le_fourteen_of_degree64 hindex hp C x he T hn)
  norm_num [preE7CharacterRho, evenWidth, halfDegree]

end PrimitiveAffineProfile

namespace Non2UnipotentPrefixFiniteMenu.CFSGPrimitiveAffineBinarySixSource

noncomputable def source64
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (U : PreE7NonPairActionClass 64)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction 64 U) (Fin 64))
    (P : PrimitiveAffineProfile (preE7NonPairAction 64 U) (Fin 64))
    (hn : ¬ IsSolvable (P.complement ⟨0, by decide⟩)) :
    PreE7RankTailOwnerSourceData 64 U := by
  let x : Fin 64 := ⟨0, by decide⟩
  let C := P.elementaryChart hp
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by decide) (by decide) hp P x C T hn
    (P.nonsoluble_margin_of_degree64_prime hindex hp C x (by simp) T hn)

end Non2UnipotentPrefixFiniteMenu.CFSGPrimitiveAffineBinarySixSource
end SymmetricSubgroupAsymptotics
