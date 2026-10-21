import SymmetricSubgroupAsymptotics.BinaryPairWideHeadKernelDimension
import SymmetricSubgroupAsymptotics.BinaryPairRegularSubgroupSixKernelHead
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryComplete
import SymmetricSubgroupAsymptotics.BinaryPermutationSubgroupRestriction
import SymmetricSubgroupAsymptotics.BinaryNonelementaryPermutationHead
import SymmetricSubgroupAsymptotics.BinaryPairRankFiveResidualTop

/-! Wide original point modules bound the actual sixteen-point source
order through its SAME inner flip kernel. No quotient-axis loss occurs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (E : BinaryPairFrame U (Fin 8))

private theorem regular_subgroup_head_cap_three
    (hregular : BinaryRegularEightNaturalRegistry.H ≤ E.top.range)
    (A : Subrepresentation E.coordinateTopAction) :
    Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 3 := by
  let j := Subgroup.inclusion hregular
  have he (t : BinaryRegularEightNaturalRegistry.H) (v : Fin 8 → ZMod 2) :
      E.coordinateTopAction (j t) v = BinaryRegularEightNaturalRegistry.rho t v :=
    binaryPermutation_subgroup_restriction _ _ hregular t v
  let B := restrictionSameVectors E.coordinateTopAction BinaryRegularEightNaturalRegistry.rho j he A
  have hh := restrictionSameVectors_head_le E.coordinateTopAction BinaryRegularEightNaturalRegistry.rho j he A
  obtain ⟨i, hi⟩ := BinaryRegularEightNaturalRegistry.complete B
  have hb := BinaryRegularEightNaturalRegistry.coinvariants_finrank_le i
  rw [hi] at hb
  have hn : ∀ i : Fin 47, BinaryRegularEightNaturalRegistry.headCeiling i ≤ 3 := by decide
  exact hh.trans (hb.trans (hn i))

private theorem nonelementary_head_cap_two (hU : IsPGroup 2 U)
    (hnon : ¬ ∀ t : E.top.range, t ^ 2 = 1)
    (A : Subrepresentation E.coordinateTopAction) :
    Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 2 := by
  letI wideModuleSourceCard_topTransitive : MulAction.IsPretransitive E.top.range (Fin 8) := E.top_pretransitive
  have hh := twoGroup_faithful_permutationSubrepresentationHead_le_quarter (E.top_isPGroup hU) hnon A
  rw [representationHead_finrank_eq_coinvariants] at hh
  simpa only [Nat.card_fin] using hh

theorem inner_top_not_elementary_of_card_thirty_two (hU : IsPGroup 2 U)
    (hcard : Nat.card E.top.range = 32) : ¬ ∀ t : E.top.range, t ^ 2 = 1 := by
  letI wideModuleSourceCard_eightTransitive : MulAction.IsPretransitive E.top.range (Fin 8) := E.top_pretransitive
  intro hel
  obtain ⟨c, hc⟩ := BinaryDegreeEightElementaryActionCoverage.elementary_action_conjugate_regular
    E.top.range (E.top_isPGroup hU) (fun i j => MulAction.exists_smul_eq E.top.range i j)
    (by intro t i; change (t ^ 2).val i = i; rw [hel]; rfl)
  have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
  change Nat.card E.top.range =
    Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)) at hh
  rw [BinaryMenuCayley8T3.exact_card, hcard] at hh
  omega

theorem source_card_le_of_kernel_dimension_and_top_card (j t : ℕ)
    (hJ : Module.finrank (ZMod 2) E.kernelSpace ≤ j) (hT : Nat.card E.top.range ≤ t) :
    Nat.card U ≤ 2 ^ j * t := by
  have hj : Nat.card E.kernelSpace ≤ 2 ^ j := by
    have hc : Nat.card E.kernelSpace = 2 ^ Module.finrank (ZMod 2) E.kernelSpace := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E.kernelSpace))
    rw [hc]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hJ
  rw [← E.kernelSpace_card_mul_top]
  exact Nat.mul_le_mul hj hT

theorem source_card_le_1024_of_regular_top_wide_module (hU : IsPGroup 2 U)
    (hH : E.top.range = BinaryRegularEightNaturalRegistry.H)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) : Nat.card U ≤ 1024 := by
  have hh := E.kernel_dimension_add_wide_head_le hU 0 3
    (E.regular_subgroup_head_cap_three hH.ge) W (by omega)
  have hJ : Module.finrank (ZMod 2) E.kernelSpace ≤ 7 := by omega
  have hcard : Nat.card E.top.range = 8 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T3.exact_card
  exact E.source_card_le_of_kernel_dimension_and_top_card 7 8 hJ hcard.le

theorem source_card_le_1024_of_small_nonelementary_top_wide_module (hU : IsPGroup 2 U)
    (hnon : ¬ ∀ t : E.top.range, t ^ 2 = 1) (hcard : Nat.card E.top.range ≤ 16)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) : Nat.card U ≤ 1024 := by
  have hh := E.kernel_dimension_add_wide_head_le hU 0 2
    (E.nonelementary_head_cap_two hU hnon) W (by omega)
  have hJ : Module.finrank (ZMod 2) E.kernelSpace ≤ 6 := by omega
  exact E.source_card_le_of_kernel_dimension_and_top_card 6 16 hJ hcard

theorem source_card_le_1024_of_order_thirty_two_regular_subgroup_wide_module
    (hU : IsPGroup 2 U) (hnon : ¬ ∀ t : E.top.range, t ^ 2 = 1)
    (hregular : BinaryRegularEightNaturalRegistry.H ≤ E.top.range)
    (hcard : Nat.card E.top.range = 32)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) : Nat.card U ≤ 1024 := by
  have hh := E.kernel_dimension_add_wide_head_le hU 0 2
    (E.nonelementary_head_cap_two hU hnon) W (by omega)
  have hJ : Module.finrank (ZMod 2) E.kernelSpace ≤ 5 := by
    by_contra hbad
    have he : Module.finrank (ZMod 2) E.kernelSpace = 6 := by omega
    have hb := E.naturalModuleHead_le_three_of_regular_subgroup_kernel_dimension_six hregular he W
    omega
  exact E.source_card_le_of_kernel_dimension_and_top_card 5 32 hJ hcard.le

end SymmetricSubgroupAsymptotics.BinaryPairFrame
