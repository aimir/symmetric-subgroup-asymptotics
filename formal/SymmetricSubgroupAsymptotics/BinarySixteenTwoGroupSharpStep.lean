import SymmetricSubgroupAsymptotics.BinaryTransitiveNormalQuarterPlusTwo
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.TinyPrimeTopSharpFloorNumerics

/-! The existing unconditional original-action normal-rank theorem pays
six ORDINARY generators at degree sixteen for actual two-groups. Only the
proved nilpotent lifting implication is used. An actual binary pair frame
with a two-group top is itself a two-group by its actual correlated kernel;
there is no transitive-eight rank-three claim or current-degree bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySixteenTwoGroupSharpStep
open TraceySharpHalfDegreeNumerics

theorem genRank_le_six {X : Type} [Finite X] (J : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive J X] (hJ : IsPGroup 2 J) (hcard : Nat.card X = 16) :
    MarkedC4.genRank J ≤ 6 := by
  letI : Group.IsNilpotent J := hJ.isNilpotent
  have hh := twoGroup_transitive_normalGen_le_quarter_add_two J hJ (⊤ : Subgroup J)
  have hn : MarkedC4.normalGen (⊤ : Subgroup J) ≤ 6 := by simpa only [hcard] using hh
  exact MarkedC4.genRank_le_normalGen_top.trans hn

theorem genRank_le_sharpFloor (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (hJ : IsPGroup 2 J) (hn : n = 16) :
    MarkedC4.genRank J ≤ sharpFloor n := by
  have hh := genRank_le_six J hJ (by simpa only [Nat.card_fin] using hn)
  have hsix : 6 ≤ sharpFloor 16 := TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square
    16 6 4 (by decide)
      (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 16 4 (by decide) (by decide)) (by decide)
  exact hh.trans (by simpa only [hn] using hsix)

theorem genRank_le_sharpFloor_of_binary_top
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPretransitive J (Fin n)]
    {I : Type} [Finite I] (F : BinaryPairFrame J I)
    (hTop : IsPGroup 2 F.top.range) (hn : n = 16) :
    MarkedC4.genRank J ≤ sharpFloor n :=
  genRank_le_sharpFloor n J (F.source_isPGroup_of_top_isPGroup hTop) hn

theorem exists_generating_finset_of_binary_top
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n))) [MulAction.IsPretransitive J (Fin n)]
    {I : Type} [Finite I] (F : BinaryPairFrame J I)
    (hTop : IsPGroup 2 F.top.range) (hn : n = 16) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n := by
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hcard.le.trans (genRank_le_sharpFloor_of_binary_top J F hTop hn)⟩

end SymmetricSubgroupAsymptotics.BinarySixteenTwoGroupSharpStep
