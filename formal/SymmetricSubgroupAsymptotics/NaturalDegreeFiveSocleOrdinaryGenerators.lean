import SymmetricSubgroupAsymptotics.SimpleLeastIndexFiveRecognition
import SymmetricSubgroupAsymptotics.OriginalNonaffineFiveByTwoSharpCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin

/-! The ORIGINAL five-point nonaffine action has rank at most two.
Actual index5 recognition makes its socle A5. A proper subgroup of S5
containing that socle has trivial actual socle quotient by Lagrange; the
full S5 case uses a literal full cycle and adjacent swap. No assertion that
two unrelated groups of equal order are isomorphic is used, nor any finite
action catalogue or global permutation-generator hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NaturalDegreeFiveSocleOrdinaryGenerators
open PrimitiveSocleRawStructure PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open TraceySharpHalfDegreeNumerics

theorem symmetric_genRank_le_two (n : ℕ) (hn : 2 ≤ n) :
    MarkedC4.genRank (Equiv.Perm (Fin n)) ≤ 2 := by
  let x : Fin n := ⟨0,by omega⟩
  let g := finRotate n
  let τ := Equiv.swap x (g x)
  let S : Finset (Equiv.Perm (Fin n)) := {g,τ}
  have hgen : Subgroup.closure (S : Set (Equiv.Perm (Fin n))) = ⊤ := by
    simpa only [S,Finset.coe_insert,Finset.coe_singleton,g,τ] using
      Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate_of_le hn)
        (support_finRotate_of_le hn) x
  have hcard : S.card ≤ 2 := by
    simpa only [S,Finset.card_singleton] using
      Finset.card_insert_le g ({τ} : Finset (Equiv.Perm (Fin n)))
  exact (MarkedC4.genRank_le hgen).trans hcard

theorem two_le_sharpFloor_five : 2 ≤ sharpFloor 5 :=
  TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square 5 2 3 (by decide)
    (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 5 3 (by decide) (by decide)) (by decide)

variable (J : Subgroup (Equiv.Perm (Fin 5))) (D : NonaffineData J (Fin 5))

theorem genRank_le_two_of_actual_index_square (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple) : MarkedC4.genRank J ≤ 2 := by
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun hh => D.noncommutative (isMulCommutative_iff.mpr hh)) hell.1
  have helln := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have helln' : ell ≤ 5 := by simpa only [Nat.card_fin] using helln
  have he : ell = 5 := le_antisymm helln' hell5
  subst ell
  have hpower := primitiveSocle_power_le_degree (by decide : 5 ≤ 5) horder (D.degreeForm hell)
  simp only [Nat.card_fin] at hpower
  have hk : D.factorCount = 1 := by
    have hpos := D.factorCount_pos
    by_contra hh
    have hb := (Nat.pow_le_pow_right (by decide : 0 < 5)
      (show 2 ≤ D.factorCount by omega)).trans hpower
    norm_num at hb
  obtain ⟨eT⟩ := SimpleLeastIndexFiveRecognition.exists_mulEquiv_alternating_five
    D.Simple D.noncommutative hell horder
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hT : Nat.card D.Simple = 60 := (Nat.card_congr eT.toEquiv).trans hA
  have hN : Nat.card (finiteGroupSocle J) = 60 :=
    (Nat.card_congr (D.oneFactorEquiv hk).toEquiv).trans hT
  have hs := SimpleLeastIndexFiveRecognition.genRank_le_two D.Simple D.noncommutative hell horder
  by_cases hfull : J = ⊤
  · let eJ : J ≃* Equiv.Perm (Fin 5) :=
      (MulEquiv.subgroupCongr hfull).trans Subgroup.topEquiv
    exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv eJ).le.trans
      (symmetric_genRank_le_two 5 (by decide))
  have hJlower : 60 ≤ Nat.card J := by
    have hh := Nat.card_le_card_of_injective
      (finiteGroupSocle J).subtype (finiteGroupSocle J).subtype_injective
    simpa only [hN] using hh
  have hJupper : 2 * Nat.card J ≤ 120 := by
    have hi := J.one_lt_index_of_ne_top hfull
    have hh := (Nat.mul_le_mul_right (Nat.card J) hi).trans_eq J.index_mul_card
    simpa only [Nat.card_perm,Nat.card_fin] using hh
  have hJ : Nat.card J = 60 := by omega
  have hprod : Nat.card (finiteGroupSocle J) * Nat.card (J ⧸ finiteGroupSocle J) = Nat.card J := by
    simpa only [(finiteGroupSocle J).index_eq_card] using (finiteGroupSocle J).card_mul_index
  rw [hN,hJ] at hprod
  have hQ : Nat.card (J ⧸ finiteGroupSocle J) = 1 := by omega
  have hQrank := FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow
    (J ⧸ finiteGroupSocle J) 0 (by simp only [hQ,pow_zero,le_refl])
  have hg := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_actual_quotient D hk
  omega

theorem genRank_le_sharpFloor_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification) :
    MarkedC4.genRank J ≤ sharpFloor 5 ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases CFSGSimpleIndexPacketOrTitsSporadic.factor_packet_or_actual_remaining_model D hCFSG with hp | hm
  · obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    exact Or.inl ((genRank_le_two_of_actual_index_square J D ell hell (hp ell hell).1).trans
      two_le_sharpFloor_five)
  · exact Or.inr hm

theorem exists_generating_finset_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧ F.card ≤ sharpFloor 5) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_sharpFloor_or_actual_remaining_model J D hCFSG with hg | hm
  · obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hcard.le.trans hg⟩
  · exact Or.inr hm

end SymmetricSubgroupAsymptotics.NaturalDegreeFiveSocleOrdinaryGenerators
