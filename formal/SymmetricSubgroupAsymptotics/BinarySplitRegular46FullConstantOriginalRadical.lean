import SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantOriginalRows
import SymmetricSubgroupAsymptotics.RepresentationRadicalFromOriginalRows
import SymmetricSubgroupAsymptotics.RepresentationCoordinateChangeRadical

/-! The checked full-constant original affine rows identify the entire
intrinsic radical of the same original invariant point submodule. No
separate displacement census or replacement module is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantOriginalRadical
open BinarySplitRegular46FullConstantStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem original_radical_eq (hzero : U = F.splitAffineAction)
    (hH : F.top.range = BinaryEightOriginalRowActions.regularH)
    (hK : F.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hW : (F.originalCoordinateSubrepresentation W).toSubmodule = state.space)
    (hcap : Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 4) :
    ((Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype).map
        F.originalCoordinateEquiv.toLinearMap = radical.space := by
  have ht (i : Fin 128) : topPermutation i ∈ F.top.range := by
    rw [hH]
    exact BinarySplitRegular46FullConstantOriginalRows.top_mem i
  have ha (i : Fin 128) : destinationOffset i ∈ F.kernelSpace := by
    rw [hK]
    exact BinarySplitRegular46FullConstantOriginalRows.offset_mem i
  let row := F.originalAffineRows hzero topPermutation destinationOffset ht ha
  have hcard : Nat.card F.kernelSpace * Nat.card F.top.range = 128 := by
    rw [hK, hH]
    have hker : Nat.card (BinaryRegularEightNaturalRegistry.charts 46).2.space = 16 :=
      (BinaryRegularEightNaturalRegistry.charts 46).2.card
    rw [hker, BinaryMenuCayley8T3.exact_card]
  have hrow : Function.Bijective row := F.originalAffineRows_bijective hzero topPermutation
    destinationOffset ht ha BinarySplitRegular46FullConstantOriginalRows.coordinates_injective hcard
  have hact (i : Fin 128) : F.originalCoordinateRepresentation (row i) = rowAction i := by
    rw [F.originalCoordinateRepresentation_affineRow hzero topPermutation destinationOffset ht ha]
    rfl
  have hc : Module.finrank (ZMod 2)
      (F.originalCoordinateSubrepresentation W).toRepresentation.Coinvariants ≤ 4 := by
    rw [← F.originalCoordinateSubrepresentation_head W]
    exact hcap
  have he := representation_radical_eq_of_original_rows_basis F.originalCoordinateRepresentation
    (F.originalCoordinateSubrepresentation W) state radical row hrow.2 rowAction hact hW
    kill_basis hc (by decide : 12 = 8 + 4)
  have hm := RepresentationCoordinateChange.subrepresentation_radical
    (permutationFunctionRepresentation (ZMod 2) U X) F.originalCoordinateEquiv W
  exact hm.trans he

end SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantOriginalRadical
