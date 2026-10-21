import SymmetricSubgroupAsymptotics.BinaryPairAugmentationSmallHeadJointDimension
import SymmetricSubgroupAsymptotics.BinaryPairRankFiveResidualTop
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts
import SymmetricSubgroupAsymptotics.PermutationCoordinateSumApply

/-! One selected augmentation-head theorem on a literal order32 top
transfers to the SAME original pair frame and bounds its joint dimension. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem chart45_eq_original_augmentation :
    BinaryRegularEightNaturalRegistry.chart45.space =
      PermutationAugmentation.space (ZMod 2) (Fin 8) := by
  have hle : BinaryRegularEightNaturalRegistry.chart45.space ≤
      PermutationAugmentation.space (ZMod 2) (Fin 8) := by
    apply BinaryRegularEightNaturalRegistry.chart45.le_of_basis_mem
    have h : ∀ j : Fin 7,
        BinaryRegularEightNaturalRegistry.chart45.inclusion (Pi.single j 1) ∈
          PermutationAugmentation.space (ZMod 2) (Fin 8) := by
      change ∀ j : Fin 7, PermutationAugmentation.coordinateSum (ZMod 2) (Fin 8)
        (BinaryRegularEightNaturalRegistry.chart45.inclusion (Pi.single j 1)) = 0
      simp only [permutation_coordinateSum_apply]
      decide +kernel
    exact h
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [BinaryRegularEightNaturalRegistry.chart45.finrank]
  have hd := PermutationAugmentation.space_finrank_add_one (k := ZMod 2) (0 : Fin 8)
  simp only [Nat.card_fin] at hd
  omega

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (E : BinaryPairFrame U (Fin 8))

omit [Finite X] [MulAction.IsPretransitive U X] in
private theorem literal_augmentation_head_le_one
    (H : Subgroup (Equiv.Perm (Fin 8))) (hH : E.top.range = H)
    (hmodel : ∀ A : Subrepresentation ((binaryPermutationRepresentation 8).comp H.subtype),
      A.toSubmodule = BinaryRegularEightNaturalRegistry.chart45.space →
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 1)
    (A : Subrepresentation E.coordinateTopAction)
    (hA : A.toSubmodule = PermutationAugmentation.space (ZMod 2) (Fin 8)) :
    Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 1 := by
  subst H
  exact hmodel A (hA.trans chart45_eq_original_augmentation.symm)

theorem head_four_joint_dimension_le_fourteen_of_literal_augmentation_head
    (hU : IsPGroup 2 U) (H : Subgroup (Equiv.Perm (Fin 8))) (hH : E.top.range = H)
    (hcard : Nat.card E.top.range = 32)
    (hmodel : ∀ A : Subrepresentation ((binaryPermutationRepresentation 8).comp H.subtype),
      A.toSubmodule = BinaryRegularEightNaturalRegistry.chart45.space →
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 1)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    Module.finrank (ZMod 2) E.kernelSpace + Module.finrank (ZMod 2) W.toSubmodule ≤ 14 := by
  letI eightAugmentationJoint_topTransitive : MulAction.IsPretransitive E.top.range (Fin 8) :=
    E.top_pretransitive
  have hnon : ¬ ∀ g : E.top.range, g ^ 2 = 1 := by
    intro hel
    obtain ⟨c, hc⟩ := BinaryDegreeEightElementaryActionCoverage.elementary_action_conjugate_regular
      E.top.range (E.top_isPGroup hU) (fun i j => MulAction.exists_smul_eq E.top.range i j)
      (by intro t i; change (t ^ 2).val i = i; rw [hel]; rfl)
    have hh := Nat.card_congr (actionConjugacyEquiv c hc).toEquiv
    change Nat.card E.top.range =
      Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)) at hh
    rw [BinaryMenuCayley8T3.exact_card, hcard] at hh
    omega
  have hcap (A : Subrepresentation E.coordinateTopAction) :
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤ 2 := by
    have hh := twoGroup_faithful_permutationSubrepresentationHead_le_quarter (E.top_isPGroup hU) hnon A
    rw [representationHead_finrank_eq_coinvariants] at hh
    simpa only [Nat.card_fin] using hh
  have hd := E.head_four_joint_dimension_add_two_le hU 0 hcap
    (E.literal_augmentation_head_le_one H hH hmodel) W hwide
  omega

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
