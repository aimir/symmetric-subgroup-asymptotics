import SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseOrdinaryFrontier
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineThirtyTwoOrdinaryGenerators

/-! The whole original primitive-affine coarse ordinary-generator branch,
with no finite catalogue or published generator bound among the inputs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseOrdinaryComplete

theorem genRank_le_ceiling
    (n : ℕ) (hn : 2≤n) (J : Subgroup (Equiv.Perm (Fin n)))
    (P : PrimitiveAffineProfile J (Fin n))
    (hprimitive : MulAction.IsPreprimitive J (Fin n)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1<n by omega))
  by_cases h16 : n=16
  · simpa only [Nat.card_fin] using (PrimitiveAffineSixteenOrdinaryGenerators.genRank_le_ceiling P hprimitive
      (by simpa only [Nat.card_fin] using h16))
  by_cases h32 : n=32
  · simpa only [Nat.card_fin] using (PrimitiveAffineThirtyTwoOrdinaryGenerators.genRank_le_ceiling P hprimitive
      (by simpa only [Nat.card_fin] using h32))
  exact PrimitiveAffineCoarseOrdinaryFrontier.genRank_le_ceiling_except_sixteen_thirtyTwo
    n hn J P hprimitive h16 h32

end SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseOrdinaryComplete
