import SymmetricSubgroupAsymptotics.SimpleLeastIndexFiveRecognition
import SymmetricSubgroupAsymptotics.ActualWreathPrimeTopSocleOrdinaryCost
import SymmetricSubgroupAsymptotics.SmallPrimeTopSharpFloorCertificates
import SymmetricSubgroupAsymptotics.OriginalNonaffinePrimeTopTinySharpStep

/-! The original local5/top2 action costs four ordinary generators.
The SAME actual index-square packet identifies its simple factor as A5,
giving both a genuine rank-two head and the exact outer debt one. Neither
a pair-family input nor a global permutation bound is assumed. CFSG leaves
only literal Tits/sporadic factor witnesses, as elsewhere in this project. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineFiveByTwoSharpCFSGReduction
open PrimitiveSocleRawStructure OriginalBlockOrdinaryCompressionState
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction TraceySharpHalfDegreeNumerics

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

local instance stateComponentAction : MulAction (initialState J block).D block.Fibre :=
  inferInstanceAs (MulAction block.Component block.Fibre)

theorem genRank_le_four_of_actual_index_square
    (hr : Nat.card block.Fibre = 5) (ht : Nat.card block.Points = 2)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) (horder : ell^2 < Nat.card D.Simple) :
    MarkedC4.genRank J ≤ 4 := by
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun hh => D.noncommutative (isMulCommutative_iff.mpr hh)) hell.1
  have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have he : ell = 5 := by omega
  subst ell
  have hpower := primitiveSocle_power_le_degree (by decide : 5 ≤ 5) horder (D.degreeForm hell)
  rw [hr] at hpower
  have hk : D.factorCount = 1 := by
    have hkpos := D.factorCount_pos
    by_contra hh
    have hb := (Nat.pow_le_pow_right (by decide : 0 < 5)
      (show 2 ≤ D.factorCount by omega)).trans hpower
    norm_num at hb
  have hs := SimpleLeastIndexFiveRecognition.genRank_le_two D.Simple D.noncommutative hell horder
  have ho := SimpleLeastIndexFiveRecognition.outer_card_eq_two D.Simple D.noncommutative hell horder
  have hOmega : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) = 1 := by
    rw [ho]
    exact ArithmeticFunction.cardFactors_apply_prime Nat.prime_two
  have htopCard : Nat.card block.Top ≤ 2 := by
    have hh := Nat.card_le_card_of_injective
      (MulAction.toPermHom block.Top block.Points) MulAction.toPerm_injective
    simpa only [Nat.card_perm,ht,Nat.factorial_succ,Nat.factorial_zero] using hh
  have htop := FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow block.Top 1
    (by simpa using htopCard)
  have hprime : (Fintype.card block.Points).Prime := by
    rw [Fintype.card_eq_nat_card,ht]
    decide
  have hsource := ActualWreathPrimeTopSocleOrdinaryCost.genRank_le_simple_add_outer_add_top_of_one_factor
    (initialState J block) D block.base hprime hk
  change MarkedC4.genRank J ≤ MarkedC4.genRank D.Simple +
    ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) + MarkedC4.genRank block.Top at hsource
  omega

theorem genRank_le_sharpFloor_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hr : Nat.card block.Fibre = 5) (ht : Nat.card block.Points = 2) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases CFSGSimpleIndexPacketOrTitsSporadic.factor_packet_or_actual_remaining_model
    D hCFSG with hp | hremaining
  · obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    have hg := genRank_le_four_of_actual_index_square J block D hr ht ell hell (hp ell hell).1
    have hn : n = 10 := by
      have hh := block.degree_product
      simpa only [hr,ht,Nat.card_fin] using hh.symm
    have hf : 4 ≤ sharpFloor n := by
      simpa only [hn] using SmallPrimeTopSharpFloorCertificates.four_le_sharpFloor_ten
    exact Or.inl (hg.trans hf)
  · exact Or.inr hremaining

theorem exists_generating_finset_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hr : Nat.card block.Fibre = 5) (ht : Nat.card block.Points = 2) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧ F.card ≤ sharpFloor n) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_sharpFloor_or_actual_remaining_model J block D hCFSG hr ht with hg | hm
  · obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hcard.le.trans hg⟩
  · exact Or.inr hm

end SymmetricSubgroupAsymptotics.OriginalNonaffineFiveByTwoSharpCFSGReduction
