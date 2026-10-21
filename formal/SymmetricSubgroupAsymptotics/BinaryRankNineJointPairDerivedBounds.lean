import SymmetricSubgroupAsymptotics.BinaryPairWideHeadJointDimension
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryComplete
import SymmetricSubgroupAsymptotics.BinaryNonelementaryPermutationHead
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoExcessOneAbelianization
import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank

/-! Actual joint pair dimensions give derived-order bounds for the SAME
rank-nine source. This does not assert a normal-F packet or a splitting. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance jointPairDerivedBoundsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))
    (E : BinaryPairFrame F.top.range (Fin 8))

include F E

theorem rank_nine_derived_card_le_of_joint_pair_dimension
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U = 9)
    (d h r : ℕ)
    (hdim : Module.finrank (ZMod 2) F.kernelSpace +
      Module.finrank (ZMod 2) E.kernelSpace ≤ d)
    (hH : Nat.card E.top.range ≤ 2 ^ h) (hbudget : d + h ≤ 9 + r) :
    Nat.card (commutator U) ≤ 2 ^ r := by
  have hFK : Nat.card F.kernelSpace = 2 ^ Module.finrank (ZMod 2) F.kernelSpace := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace))
  have hEK : Nat.card E.kernelSpace = 2 ^ Module.finrank (ZMod 2) E.kernelSpace := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E.kernelSpace))
  have hproduct : Nat.card F.kernelSpace * Nat.card E.kernelSpace ≤ 2 ^ d := by
    rw [hFK, hEK, ← pow_add]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdim
  have hcard : Nat.card U ≤ 2 ^ (9 + r) := by
    calc
      Nat.card U = (Nat.card F.kernelSpace * Nat.card E.kernelSpace) * Nat.card E.top.range := by
        rw [← F.kernelSpace_card_mul_top, ← E.kernelSpace_card_mul_top]
        exact (Nat.mul_assoc _ _ _).symm
      _ ≤ 2 ^ d * 2 ^ h := Nat.mul_le_mul hproduct hH
      _ = 2 ^ (d + h) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (9 + r) := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hbudget
  have hdegree : Nat.card X = 32 := by rw [F.card_points]; simp only [Nat.card_fin]
  have hexp := binary_degree_thirty_two_rank_nine_abelianization_exponent U hU hdegree hrank
  have hAb : Nat.card (Abelianization U) = 512 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hU hexp, hrank]
    decide
  have hc := (commutator U).card_mul_index
  change Nat.card (commutator U) * Nat.card (Abelianization U) = Nat.card U at hc
  rw [hAb] at hc
  have hb : 2 ^ (9 + r) = 512 * 2 ^ r := by rw [pow_add]; rfl
  rw [hb] at hcard
  omega

omit E in
private theorem outer_axis_dimension :
    (F.axisNaturalSubrepresentation F.top.ker).toSubmodule = F.kernelSpace := by
  apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
  rintro v ⟨a, rfl⟩
  exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property

theorem rank_nine_regular_inner_top_derived_card_le_1024
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U = 9)
    (hH : E.top.range = BinaryRegularEightNaturalRegistry.H)
    (hwide : 4 ≤ MarkedC4.normalGen F.top.ker) :
    Nat.card (commutator U) ≤ 1024 := by
  letI jointPairRegular_topTransitive : MulAction.IsPretransitive F.top.range (Fin 16) :=
    F.top_pretransitive
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hW : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by
    rw [← F.axisNatural_normalGen F.top.ker le_rfl hU]
    exact hwide
  have hcap (A : Subrepresentation E.coordinateTopAction) :
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 3 := by
    let B := E.literalPairLayer BinaryRegularEightNaturalRegistry.H hH
      (show Subrepresentation E.pulledBackCoordinateTopAction from {
        toSubmodule := A.toSubmodule
        apply_mem_toSubmodule u := A.apply_mem_toSubmodule (E.top.rangeRestrict u) })
    have hBA : Module.finrank (ZMod 2) B.toRepresentation.Coinvariants =
        Module.finrank (ZMod 2) A.toRepresentation.Coinvariants := by
      rw [E.literalPairLayer_head, E.descendPairLayer_head]
      rfl
    obtain ⟨i, hi⟩ := BinaryRegularEightNaturalRegistry.complete B
    have hb := BinaryRegularEightNaturalRegistry.coinvariants_finrank_le i
    rw [hi, hBA] at hb
    have hn : ∀ i : Fin 47, BinaryRegularEightNaturalRegistry.headCeiling i ≤ 3 := by decide
    exact hb.trans (hn i)
  have hd := E.wide_natural_head_joint_dimension_le (F.top_isPGroup hU) 0 3 hcap W (by omega)
  have haxis := F.outer_axis_dimension
  change Module.finrank (ZMod 2) E.kernelSpace + Module.finrank (ZMod 2) W.toSubmodule ≤ 16 at hd
  change W.toSubmodule = F.kernelSpace at haxis
  rw [haxis] at hd
  have hHcard : Nat.card E.top.range = 8 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T3.exact_card
  exact F.rank_nine_derived_card_le_of_joint_pair_dimension E hU hrank 16 3 10
    (by omega) hHcard.le (by decide)

theorem rank_nine_nonelementary_inner_top_derived_card_le
    (hU : IsPGroup 2 U) (hrank : MarkedC4.genRank U = 9)
    (hnon : ¬ ∀ t : E.top.range, t ^ 2 = 1)
    (hwide : 4 ≤ MarkedC4.normalGen F.top.ker)
    (h : ℕ) (hcard : Nat.card E.top.range ≤ 2 ^ h) :
    Nat.card (commutator U) ≤ 2 ^ (h + 6) := by
  letI jointPairNonelementary_topTransitive : MulAction.IsPretransitive F.top.range (Fin 16) :=
    F.top_pretransitive
  letI jointPairNonelementary_innerTransitive : MulAction.IsPretransitive E.top.range (Fin 8) :=
    E.top_pretransitive
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hW : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by
    rw [← F.axisNatural_normalGen F.top.ker le_rfl hU]
    exact hwide
  have hcap (A : Subrepresentation E.coordinateTopAction) :
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 2 := by
    have hh := twoGroup_faithful_permutationSubrepresentationHead_le_quarter
      (E.top_isPGroup (F.top_isPGroup hU)) hnon A
    rw [representationHead_finrank_eq_coinvariants] at hh
    simpa only [Nat.card_fin] using hh
  have hd := E.very_wide_natural_head_joint_dimension_lt
    (F.top_isPGroup hU) 0 2 hcap W (by omega)
  have haxis := F.outer_axis_dimension
  change Module.finrank (ZMod 2) E.kernelSpace + Module.finrank (ZMod 2) W.toSubmodule < 16 at hd
  change W.toSubmodule = F.kernelSpace at haxis
  rw [haxis] at hd
  exact F.rank_nine_derived_card_le_of_joint_pair_dimension E hU hrank 15 h (h + 6)
    (by omega) hcard (by omega)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
