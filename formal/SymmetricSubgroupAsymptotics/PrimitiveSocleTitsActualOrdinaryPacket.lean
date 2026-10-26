import SymmetricSubgroupAsymptotics.CFSGTitsFourOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGTitsCompleteOuterBudget
import SymmetricSubgroupAsymptotics.CFSGTitsOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorFourOrdinaryFromTwelve

/-! Actual Tits facts transported to the SAME nonaffine simple factor.
No model callback or supplied numerical budget occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleTitsActualOrdinaryPacket
open PrimitiveSocleRawStructure CFSGReduction

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Index.tits.Model)

include e

theorem simple_genRank_le_four : MarkedC4.genRank D.Simple ≤ 4 := by
  let e0 : D.Simple ≃* CFSG.Models.Tits := e
  letI : Finite CFSG.Models.Tits := Finite.of_equiv D.Simple e0.toEquiv
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e0]
  exact CFSGTitsFourOrdinaryGenerators.tits_genRank_le_four

theorem least_index_fourteen_le (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    14 ≤ ell := by
  let e0 : D.Simple ≃* CFSG.Models.Tits := e
  letI : Finite CFSG.Models.Tits := Finite.of_equiv D.Simple e0.toEquiv
  letI : IsSimpleGroup CFSG.Models.Tits :=
    (MulEquiv.isSimpleGroup_congr (G:=D.Simple) (H:=CFSG.Models.Tits) e0).mp D.simple
  exact CFSGTitsLeastIndexFourteen.least_index_fourteen_le ell
    (leastProperIndex_of_mulEquiv e0 ell hell)

theorem outer_cardFactors_le_two :
    ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 2 := by
  let e0 : D.Simple ≃* CFSG.Models.Tits := e
  letI : Finite CFSG.Models.Tits := Finite.of_equiv D.Simple e0.toEquiv
  letI : IsSimpleGroup CFSG.Models.Tits :=
    (MulEquiv.isSimpleGroup_congr (G:=D.Simple) (H:=CFSG.Models.Tits) e0).mp D.simple
  have hc : Nat.card (Outer D.Simple) ≤ 6 := by
    rw [outer_card_congr e0]
    exact CFSGTitsCompleteOuterBudget.outer_card_le_six
  exact SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 2 Nat.card_pos (by omega)

theorem packet (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    ell^2 < Nat.card D.Simple ∧
      SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
  let e0 : D.Simple ≃* CFSG.Models.Tits := e
  letI : Finite CFSG.Models.Tits := Finite.of_equiv D.Simple e0.toEquiv
  letI : IsSimpleGroup CFSG.Models.Tits :=
    (MulEquiv.isSimpleGroup_congr (G:=D.Simple) (H:=CFSG.Models.Tits) e0).mp D.simple
  have hn : ¬ IsMulCommutative CFSG.Models.Tits := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e0).mpr hc)
  have hm := leastProperIndex_of_mulEquiv e0 ell hell
  have hi := CFSGTitsOriginalIndexSquare.index_square hn ell hm
  have ho := CFSGTitsCompleteOuterBudget.tits_sufficient_outer_budget ell hm
  simpa only [Nat.card_congr e0.toEquiv,outer_card_congr e0] using And.intro hi ho

end SymmetricSubgroupAsymptotics.PrimitiveSocleTitsActualOrdinaryPacket
