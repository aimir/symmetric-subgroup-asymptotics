import SymmetricSubgroupAsymptotics.Selected1542SecondMonolith
import SymmetricSubgroupAsymptotics.MonolithicSocleOne

/-! The two exceptional unquotiented axes have actual socle capacity one. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

theorem originalFirstAxis_nontrivial : originalFirstAxis≠⊥ := by
  intro hb
  have hz : originalCentralInvolution∈originalFirstAxis := Subgroup.mem_zpowers _
  rw [hb] at hz
  have he := congrArg (fun g : Original => g.val 0) (Subgroup.mem_bot.mp hz)
  exact firstCenter_z_nontrivial he

theorem original_socle_eq_firstAxis : finiteGroupSocle Original=originalFirstAxis :=
  MonolithicSocleOne.socle_eq originalFirstAxis originalFirstAxis_nontrivial
    (fun N _ hN => original_first_monolith N inferInstance hN)

theorem original_socle_one : MarkedC4.normalGen (finiteGroupSocle Original)≤1 :=
  MonolithicSocleOne.normalGen_le_one originalFirstAxis originalFirstAxis_nontrivial
    (fun N _ hN => original_first_monolith N inferInstance hN)

theorem firstQuotient_socle_eq_secondAxis : finiteGroupSocle FirstQuotient=secondAxis :=
  MonolithicSocleOne.socle_eq secondAxis secondAxis_minimalNormal.2.1
    (fun N _ hN => original_second_monolith N inferInstance hN)

theorem firstQuotient_socle_one : MarkedC4.normalGen (finiteGroupSocle FirstQuotient)≤1 :=
  MonolithicSocleOne.normalGen_le_one secondAxis secondAxis_minimalNormal.2.1
    (fun N _ hN => original_second_monolith N inferInstance hN)

theorem original_socle_bound_one : SocleNormalGeneratorBound Original 1 :=
  (socleNormalGeneratorBound_iff_normalGen_le _ _).mpr original_socle_one

theorem firstQuotient_socle_bound_one : SocleNormalGeneratorBound FirstQuotient 1 :=
  (socleNormalGeneratorBound_iff_normalGen_le _ _).mpr firstQuotient_socle_one

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
