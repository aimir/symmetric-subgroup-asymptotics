import SymmetricSubgroupAsymptotics.NormalGoodSylowOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.CFSGNonaffineCoarseComposition

/-! The same original one-factor full socle inherits its actual
simple-model good-Sylow witness. Its original outer embedding pays the
quotient generator budget, with no abstract replacement of the action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

theorem NonaffineData.genRank_half_degree_of_oneFactor_goodSylow
    (D : NonaffineData G X) (hk : D.factorCount=1) (p b : ℕ) (hp : 3 ≤ p)
    (hgood : CFSGReduction.GoodSylowPrime D.Simple p)
    (houter : Nat.card (Outer D.Simple) ≤ 2^b)
    (hn : 6*(b+1) ≤ Nat.card X) : 2*MarkedC4.genRank G ≤ Nat.card X := by
  have hs : CFSGReduction.GoodSylowPrime (finiteGroupSocle G) p :=
    CFSGReduction.goodSylowPrime_map (D.oneFactorEquiv hk).symm hgood
  have hq : Nat.card (G⧸finiteGroupSocle G) ≤ 2^b := by
    have h := CFSGNonaffineCoarseComposition.quotient_card_le_outer_wreath D
    simpa only [hk,pow_one,Nat.factorial_one,mul_one] using h.trans
      (by simpa only [hk,pow_one,Nat.factorial_one,mul_one] using houter)
  exact NormalGoodSylowOrdinaryGenerators.two_mul_genRank_le_degree
    (X:=X) (finiteGroupSocle G) p b hp hn hs hq

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
