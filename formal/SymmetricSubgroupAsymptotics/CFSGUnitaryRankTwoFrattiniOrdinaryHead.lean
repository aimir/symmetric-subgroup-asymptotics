import SymmetricSubgroupAsymptotics.CFSGUnitaryRadicalFrattiniOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGTwistedA2ProjectiveRadical
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoSylowAlignment
import SymmetricSubgroupAsymptotics.CFSGTwistedA2ModelGoodSylow
import SymmetricSubgroupAsymptotics.GoodSylowSelectedRankOrdinaryGenerators

/-! The SAME original rank-two projective unitary Sylow is the literal
Heisenberg radical. Its actual Frattini parameter quotient costs2f;
selected GoodSylow generation gives an original model head2f+1, with no
pair, permutation bound or replacement model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoFrattiniOrdinaryHead
open CFSGTwistedAUnitaryCoordinates CFSGTwistedAUpperUnipotent

theorem model_genRank_le (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    MarkedC4.genRank (CFSG.Models.TwistedA 2 q) ≤ 2*q.exponent+1 := by
  letI : Finite (CFSG.Models.TwistedA 2 q) :=
    Finite.of_surjective (rankTwoProjectiveCover q hq) (rankTwoProjectiveCover_surjective q hq)
  let P := rankTwoProjectiveSylow q hq
  let eP : fixedRadical q 0 ≃* P :=
    (rankTwoRadicalProjectiveEquiv q hq).trans
      (MulEquiv.subgroupCongr (rankTwoProjectiveSylow_coe q hq).symm)
  have hP : MarkedC4.genRank P ≤ 2*q.exponent := by
    rw [←CoprimeNilpotentProductGenerators.genRank_mulEquiv eP]
    simpa only [Nat.zero_add,Nat.one_mul] using
      CFSGUnitaryRadicalFrattiniOrdinaryGenerators.radical_genRank_le q 0
  have hh := GoodSylowSelectedRankOrdinaryGenerators.genRank_le_selected q.prime
    (CFSGReduction.twistedA2_goodSylowPrime q (by omega)) P
  exact hh.trans (Nat.add_le_add_right hP 1)

theorem exists_generating_finset (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    ∃ S : Finset (CFSG.Models.TwistedA 2 q),
      Subgroup.closure (S : Set (CFSG.Models.TwistedA 2 q)) = ⊤ ∧ S.card ≤ 2*q.exponent+1 := by
  letI : Finite (CFSG.Models.TwistedA 2 q) :=
    Finite.of_surjective (rankTwoProjectiveCover q hq) (rankTwoProjectiveCover_surjective q hq)
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := CFSG.Models.TwistedA 2 q)
  exact ⟨S,hgen,hcard.le.trans (model_genRank_le q hq)⟩

end SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoFrattiniOrdinaryHead
