import SymmetricSubgroupAsymptotics.BinarySplitRegular46ParityZeroStabilizerThreeOrbitWitnesses
import SymmetricSubgroupAsymptotics.BinaryPairOriginalCoordinateRepresentation

/-! The checked three literal rows for each parity section value are
actual elements of the SAME original regular-K46 zero model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularParityZeroOrbitOriginalRows
open BinarySplitRegular46ParityZeroStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (E : BinaryPairFrame U (Fin 8))

theorem exists_actual_three_orbit_witnesses
    (hzero : U = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.regularH)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (c : Fin 8 → ZMod 2) (hc : c ≠ 0) :
    ∃ u : Fin 3 → U, ∀ i j : Fin 3, i ≠ j →
      E.originalCoordinateRepresentation (u i) (sectionMap c) -
        E.originalCoordinateRepresentation (u j) (sectionMap c) ∉ radical.space := by
  obtain ⟨r,ht,ha,hsep⟩ := exists_three_literal_rows c hc
  have ht' (i : Fin 3) : topPermutation (r i) ∈ E.top.range := by
    rw [hH]
    exact ht i
  have ha' (i : Fin 3) : destinationOffset (r i) ∈ E.kernelSpace := by
    rw [hK]
    exact ha i
  let u : Fin 3 → U := fun i => E.originalZeroRow hzero
    ⟨topPermutation (r i), ht' i⟩ (destinationOffset (r i)) (ha' i)
  have hact (i : Fin 3) : E.originalCoordinateRepresentation (u i) = rowAction (r i) :=
    E.originalCoordinateRepresentation_zeroRow hzero _ _ (ha' i)
  refine ⟨u, ?_⟩
  intro i j hij
  rw [hact,hact]
  exact hsep i j hij

end SymmetricSubgroupAsymptotics.BinaryRegularParityZeroOrbitOriginalRows
