import SymmetricSubgroupAsymptotics.CFSGYCoprimeOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSocleSufficientPairAllDegreeOrdinary
import SymmetricSubgroupAsymptotics.OriginalNonaffineTinyPairBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.CFSGReeFFourCompleteSufficientSimpleIndex

/-! The actual coprime-arm Fischer23 pair pays every primitive degree
and every original nonaffine block degree/top. The existing numerical
callback remains explicit and unchanged; it is not proved here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FischerTwentyThreeOrdinaryClosure
open PrimitiveSocleRawStructure CFSGReduction TraceyStrictlySmallerTransitiveActions

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)

include remaining in
theorem primitive_genRank_le_ceiling
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (e : D.Simple ≃* (CFSG.Index.sporadic .fi23).Model) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : Finite (CFSG.Index.sporadic .fi23).Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup (CFSG.Index.sporadic .fi23).Model := e.symm.isSimpleGroup
  have hni : ¬IsMulCommutative (CFSG.Index.sporadic .fi23).Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp : ModelSufficientSimpleIndexBounds (.sporadic .fi23) :=
    remaining (.sporadic .fi23) hni (by trivial)
  exact PrimitiveSocleSufficientPairAllDegreeOrdinary.genRank_le_ceiling D hk e
    CFSGYCoprimeOrdinaryGenerators.fischer23_bounds.fullCentralQuotientFamily
    (fun ell hell => (hp ell hell).2)

include remaining in
theorem block_genRank_le_ceiling
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)
    (e : D.Simple ≃* (CFSG.Index.sporadic .fi23).Model)
    (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  letI : Finite (CFSG.Index.sporadic .fi23).Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup (CFSG.Index.sporadic .fi23).Model := e.symm.isSimpleGroup
  have hni : ¬IsMulCommutative (CFSG.Index.sporadic .fi23).Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp : ModelSufficientSimpleIndexBounds (.sporadic .fi23) :=
    remaining (.sporadic .fi23) hni (by trivial)
  exact OriginalNonaffineTinyPairBlockOrdinaryStep.genRank_le_ceiling_of_model
    J block D e CFSGYCoprimeOrdinaryGenerators.fischer23_bounds.fullCentralQuotientFamily hp
    i hbelow

end SymmetricSubgroupAsymptotics.FischerTwentyThreeOrdinaryClosure
