import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourCoarseNonzeroMenu
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourComplementRank
import SymmetricSubgroupAsymptotics.RetainedSocleRelativeHead

/-! The nonzero ternary-core branch bounds every original normal relative
binary head. Retained quotients use the established whole-socle theorem;
killed translations use the actual signed-wreath quotient. No catalogue,
all-normal certificate or unrestricted degree-sixteen owner is assumed. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The retained and killed branches use their original kernels. -/
theorem degreeFourNonzero_binary_relative_head_le
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (N : Subgroup (preE7NonPairAction w U)) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ Nat.card block.Points := by
  have h := primeRelativeHead_le_of_retained_socles 2 (E block P)
    (degreeFourSocleSlots (Nat.card block.Points)) (Nat.card block.Points)
    (fun K hK => degreeFourNonzeroRetainedSocleGeneratorBound block P
      hTracey hMN hClifford hTraceyPerm hr hs hD K hK)
    (degreeFourComplement_binary_sectional_rank block P hr) N
  have hslots : degreeFourSocleSlots (Nat.card block.Points) ≤ Nat.card block.Points := by
    unfold degreeFourSocleSlots
    split <;> omega
  exact h.trans (max_le hslots le_rfl)

/-- In the actual four-by-four branch the original rank contribution is
at most four, independently of its normal subgroup and of diagonal cores. -/
theorem degreeFourFourBlockNonzero_binary_relative_head_le_four
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : Nat.card block.Points = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (N : Subgroup (preE7NonPairAction w U)) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 4 := by
  simpa only [hs] using degreeFourNonzero_binary_relative_head_le block P
    hTracey hMN hClifford hTraceyPerm hr (by omega) hD N

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
