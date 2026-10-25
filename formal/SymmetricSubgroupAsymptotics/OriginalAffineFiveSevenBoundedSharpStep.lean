import SymmetricSubgroupAsymptotics.PrimitiveAffineSmallLocalOrderDivisibility
import SymmetricSubgroupAsymptotics.OriginalBlockOrdinaryCompressionState
import SymmetricSubgroupAsymptotics.ActualWreathPrimeTopChiefOrdinaryBudget
import SymmetricSubgroupAsymptotics.ActualWreathChiefPrimeMultiplicityBudget
import SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedSharpCFSGReduction

/-! Every ORIGINAL affine minimal-block component of degree5 or7 pays
the literal sharp floor at total degree below22. The actual component
orders divide20/42. Prime tops use one common actual chief trace; the
only composite top is4, where the same-source binary prime-multiplicity
cost is five. No induction, global Tracey/MN, action catalogue, local
capacity certificate, or finite-model generator assumption occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineFiveSevenBoundedSharpStep
open PrimitiveSocleRawStructure OriginalBlockOrdinaryCompressionState
open ActualWreathChiefPrimeMultiplicityBudget FiniteGroupPrimeMultiplicityGenerators
open TraceySharpHalfDegreeNumerics

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.1; omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
private theorem component_cardFactors_le_three
    (hr : Nat.card block.Fibre = 5 ∨ Nat.card block.Fibre = 7) :
    ArithmeticFunction.cardFactors (Nat.card block.Component) ≤ 3 := by
  let x : block.Fibre := ⟨x₀,block.map_base⟩
  rcases hr with hr | hr
  · have hd := PrimitiveAffineSmallLocalOrderDivisibility.card_dvd_twenty P x hr
    exact (cardFactors_mono_of_dvd (Nat.card_pos (α := block.Component)).ne'
      (by decide : (20 : ℕ) ≠ 0) hd).trans_eq (by decide +kernel)
  · have hd := PrimitiveAffineSmallLocalOrderDivisibility.card_dvd_forty_two P x hr
    exact (cardFactors_mono_of_dvd (Nat.card_pos (α := block.Component)).ne'
      (by decide : (42 : ℕ) ≠ 0) hd).trans_eq (by decide +kernel)

private theorem prime_top_rank (ht : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3) :
    MarkedC4.genRank block.Top ≤ Nat.card block.Points-1 := by
  have hcard : Nat.card block.Top ≤ (Nat.card block.Points).factorial := by
    simpa only [Nat.card_perm] using Nat.card_le_card_of_injective
      (MulAction.toPermHom block.Top block.Points) MulAction.toPerm_injective
  rcases ht with ht | ht
  · rw [ht] at hcard ⊢
    exact FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow block.Top 1
      (by simpa only [Nat.factorial_succ,Nat.factorial_zero] using hcard)
  · rw [ht] at hcard ⊢
    norm_num only [Nat.factorial_succ,Nat.factorial_zero] at hcard
    by_contra hh
    have hg : 3 ≤ MarkedC4.genRank block.Top := by omega
    have hp := (Nat.pow_le_pow_right (by decide : 0 < 2) hg).trans
      ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card block.Top).trans hcard)
    norm_num at hp

include P in
theorem genRank_le_sharpFloor
    (hr : Nat.card block.Fibre = 5 ∨ Nat.card block.Fibre = 7) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n := by
  have hproduct : Nat.card block.Fibre*Nat.card block.Points = n := by
    simpa only [Nat.card_fin] using block.degree_product
  have ht2 := block.degrees_ge_two.2
  have hr5 : 5 ≤ Nat.card block.Fibre := by rcases hr with h | h <;> omega
  have ht4 : Nat.card block.Points ≤ 4 := by nlinarith only [hproduct,hr5,hsmall]
  have htcases : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 := by omega
  have hOmega := component_cardFactors_le_three J block P hr
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using ht2
  rcases htcases with ht | ht | ht
  · have hprime : (Fintype.card block.Points).Prime := by
      rw [Fintype.card_eq_nat_card,ht]; decide
    have hsource := ActualWreathPrimeTopChiefOrdinaryBudget.genRank_le_cardFactors_add_top
      (initialState J block) block.base hprime
    change MarkedC4.genRank J ≤ ArithmeticFunction.cardFactors (Nat.card block.Component) +
      MarkedC4.genRank block.Top at hsource
    have htop := prime_top_rank J block (Or.inl ht)
    have hg : MarkedC4.genRank J ≤ 4 := by omega
    rcases hr with hr | hr
    · have hn : n = 10 := by rw [hr,ht] at hproduct; omega
      exact hg.trans (by simpa only [hn] using
        SmallPrimeTopSharpFloorCertificates.four_le_sharpFloor_ten)
    · have hn : n = 14 := by rw [hr,ht] at hproduct; omega
      exact hg.trans ((by decide : 4 ≤ 6).trans
        (OriginalNonaffineBoundedSharpCFSGReduction.six_le_sharpFloor_of_band n (by omega) (by omega)))
  · have hprime : (Fintype.card block.Points).Prime := by
      rw [Fintype.card_eq_nat_card,ht]; decide
    have hsource := ActualWreathPrimeTopChiefOrdinaryBudget.genRank_le_cardFactors_add_top
      (initialState J block) block.base hprime
    change MarkedC4.genRank J ≤ ArithmeticFunction.cardFactors (Nat.card block.Component) +
      MarkedC4.genRank block.Top at hsource
    have htop := prime_top_rank J block (Or.inr ht)
    have hg : MarkedC4.genRank J ≤ 5 := by omega
    have hn : 14 ≤ n := by rw [ht] at hproduct; omega
    exact hg.trans ((by decide : 5 ≤ 6).trans
      (OriginalNonaffineBoundedSharpCFSGReduction.six_le_sharpFloor_of_band n hn (by omega)))
  · have hr5 : Nat.card block.Fibre = 5 := by
      rcases hr with h | h
      · exact h
      · rw [h,ht] at hproduct
        omega
    have hn : n = 20 := by rw [hr5,ht] at hproduct; omega
    let x : block.Fibre := ⟨x₀,block.map_base⟩
    have hdiv := PrimitiveAffineSmallLocalOrderDivisibility.card_dvd_twenty P x hr5
    have hfour : Fintype.card block.Points = 2^2 := by
      norm_num only [Fintype.card_eq_nat_card,ht]
    obtain ⟨c,hc,hcost,hsource⟩ := exists_binaryOrderCost_bound (initialState J block)
      block.base hI 2 hfour
    change c ≤ binaryOrderCost (Nat.card block.Component) 2 at hcost
    change MarkedC4.genRank J ≤ c+MarkedC4.genRank block.Top at hsource
    have hmono := binaryOrderCost_mono_of_dvd (Nat.card_pos (α := block.Component)).ne'
      (by decide : (20 : ℕ) ≠ 0) hdiv 2
    have h20 : binaryOrderCost 20 2 = 5 := by decide +kernel
    have htop := SmallFourPointOrdinaryGenerators.genRank_le_two
      (G := block.Top) (X := block.Points) ht
    have hg : MarkedC4.genRank J ≤ 7 := by omega
    exact hg.trans ((by decide : 7 ≤ 8).trans (by simpa only [hn] using
      SmallPrimeTopSharpFloorCertificates.eight_le_sharpFloor_twenty))

include P in
theorem exists_generating_finset
    (hr : Nat.card block.Fibre = 5 ∨ Nat.card block.Fibre = 7) (hsmall : n < 22) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n := by
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hcard.le.trans (genRank_le_sharpFloor J block P hr hsmall)⟩

end SymmetricSubgroupAsymptotics.OriginalAffineFiveSevenBoundedSharpStep
