import SymmetricSubgroupAsymptotics.CFSGSporadicPrimeProductDivisors
import SymmetricSubgroupAsymptotics.PrimitiveSocleLargePrimePairBoundedSharp

/-! A source-only small first bridge for the ORIGINAL J2 presentation.
Its prime-seven product relator pays the actual normalizer budget in
degrees eleven and twelve. No assertion about J2 order, least index,
Outer, subgroup recognition, or degrees thirteen through twenty-one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoPrimeSevenBoundedBand
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open TenPointHalfDegreeCompleteCFSG (fixedBudget)

theorem model_seven_dvd_card
    (hn : ¬IsMulCommutative CFSG.Models.Presentations.J2.Model) :
    7 ∣ Nat.card CFSG.Models.Presentations.J2.Model := by
  apply GeneratingPairPrimeProductOrder.prime_dvd_presented_card
    CFSG.Models.Presentations.J2.relators 7 (by decide) ?_ hn
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

section Actual
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X)

theorem actual_seven_dvd_card
    (e : D.Simple ≃* CFSG.Models.Presentations.J2.Model) :
    7 ∣ Nat.card D.Simple := by
  have hn : ¬IsMulCommutative CFSG.Models.Presentations.J2.Model := by
    intro hc
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hc)
  rw [Nat.card_congr e.toEquiv]
  exact model_seven_dvd_card hn

theorem seven_le_actual_degree
    (e : D.Simple ≃* CFSG.Models.Presentations.J2.Model) :
    7 ≤ Nat.card X := by
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  exact (by decide : Nat.Prime 7).dvd_factorial.mp
    ((actual_seven_dvd_card D e).trans hd)

theorem genRank_le_sharpFloor_of_degree_eleven_or_twelve
    (hCFSG : CFSG.CFSGClassification)
    (hlo : 11 ≤ Nat.card X) (hhi : Nat.card X ≤ 12)
    (e : D.Simple ≃* CFSG.Models.Presentations.J2.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hpdiv := actual_seven_dvd_card D e
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  have hnot : ¬7^2 ∣ Nat.card D.Simple := by
    intro hh
    exact (by decide : ¬7^2 ∣ Nat.factorial 12)
      (hh.trans (hd.trans (Nat.factorial_dvd_factorial hhi)))
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm CFSGGeneration.j2_twoGenerated
  have hhead : MarkedC4.genRank D.Simple ≤ 2 :=
    (MarkedC4.genRank_le hS).trans hcard
  have hb := LargePrimeSocleQuotientGenerators.nonaffine_genRank_le_fixedBudget
    (p := 7) (X := X) hCFSG D (by omega) hhead hpdiv hnot (by omega) (by omega)
  have hfixed : fixedBudget (Nat.card X-7) ≤ 2 := by
    unfold fixedBudget
    split_ifs <;> omega
  have hfive : MarkedC4.genRank G ≤ 5 := by omega
  exact hfive.trans
    (PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction.five_le_sharpFloor_of_band
      (Nat.card X) hlo (by omega))

end Actual
end SymmetricSubgroupAsymptotics.CFSGJankoTwoPrimeSevenBoundedBand
