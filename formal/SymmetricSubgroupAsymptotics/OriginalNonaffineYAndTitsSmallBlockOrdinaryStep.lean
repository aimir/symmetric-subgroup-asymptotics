import SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedHeadSmallLocalOrdinaryStep
import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGTitsSevenOrdinaryGenerators

/-! Thin SAME-source Y/Tits block consumers. The genuine original model
heads are supplied internally. The numerical callback is EXACTLY the one
already retained by the optional CFSG ordinary facade, and is explicit:
this conditional reduction neither proves that callback nor adds a new
T1 assumption. Both one- and multiple-factor local socles are handled by
the shared installer. No global ordinary bound is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineYAndTitsSmallBlockOrdinaryStep
open PrimitiveSocleRawStructure CFSGReduction TraceyStrictlySmallerTransitiveActions

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

include remaining

private theorem actual_packet (j : CFSG.Index)
    (hj : RemainingSufficientSimpleIndexAfterReeFFourOuter j)
    (hshape : ModelBoundsAfterReeFFourIndexSquare j = ModelSufficientSimpleIndexBounds j)
    (e : D.Simple ≃* j.Model) :
    ∀ ell : ℕ, LeastProperIndex D.Simple ell → ell^2 < Nat.card D.Simple ∧
      SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hni : ¬ IsMulCommutative j.Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp : ModelSufficientSimpleIndexBounds j := hshape.mp (remaining j hni hj)
  exact sufficientSimpleIndexBounds_of_mulEquiv e hp

/-- All four actual Y-derived FULL central quotients, local degrees20..31,
with EVERY inherited top and strictly-smaller transitive induction. -/
theorem y_genRank_le_ceiling (i : block.Points)
    (hr : 20 ≤ Nat.card block.Fibre) (hsmall : Nat.card block.Fibre < 32)
    (s : CFSG.Sporadic) (hs : PrimitiveSocleYSectionOrdinaryTail.IsYSectionModel s)
    (e : D.Simple ≃* (CFSG.Index.sporadic s).Model)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have hsimple : MarkedC4.genRank D.Simple ≤ 10 := by
    obtain ⟨S,hS,hcard⟩ := CFSGGeneration.generators_card_le_of_surjective
      e.symm.toMonoidHom e.symm.surjective
      (PrimitiveSocleYSectionOrdinaryTail.ySection_generators s hs)
    exact (MarkedC4.genRank_le hS).trans hcard
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  obtain ⟨horder,houter⟩ := actual_packet remaining J block D (.sporadic s) (by trivial) (by rfl) e ell hell
  exact OriginalNonaffineBoundedHeadSmallLocalOrdinaryStep.genRank_le_ceiling J block D i
    hsmall (Or.inl ⟨hr,hsimple⟩) hbelow ell hell horder houter

/-- Actual Tits, local degrees18..31. The bound uses the checked original
seven-generator family and FULL central quotient, not a generating pair. -/
theorem tits_genRank_le_ceiling (i : block.Points)
    (hr : 18 ≤ Nat.card block.Fibre) (hsmall : Nat.card block.Fibre < 32)
    (e : D.Simple ≃* CFSG.Index.tits.Model)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have hsimple : MarkedC4.genRank D.Simple ≤ 7 := by
    obtain ⟨S,hS,hcard⟩ := CFSGGeneration.generators_card_le_of_surjective
      e.symm.toMonoidHom e.symm.surjective
      CFSGTitsSevenOrdinaryGenerators.exists_tits_generating_finset
    exact (MarkedC4.genRank_le hS).trans hcard
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  obtain ⟨horder,houter⟩ := actual_packet remaining J block D .tits (by trivial) (by rfl) e ell hell
  exact OriginalNonaffineBoundedHeadSmallLocalOrdinaryStep.genRank_le_ceiling J block D i
    hsmall (Or.inr ⟨hr,hsimple⟩) hbelow ell hell horder houter

end SymmetricSubgroupAsymptotics.OriginalNonaffineYAndTitsSmallBlockOrdinaryStep
