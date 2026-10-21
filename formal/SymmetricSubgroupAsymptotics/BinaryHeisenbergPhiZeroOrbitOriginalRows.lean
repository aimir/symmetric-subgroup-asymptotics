import SymmetricSubgroupAsymptotics.BinarySplitHeisenberg14PhiZeroStabilizerThreeOrbitWitnesses
import SymmetricSubgroupAsymptotics.BinaryPairOriginalCoordinateRepresentation

/-! Three literal orbit rows per nonzero section value are lifted into
the SAME original zero model. Only their proved top/kernel membership
is used; no enumeration or bijection of the entire source is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroOrbitOriginalRows
open BinarySplitHeisenberg14PhiZeroStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (E : BinaryPairFrame U (Fin 8))

theorem exists_actual_three_orbit_witnesses
    (hzero : U = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.heisenbergH)
    (hK : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 14).2.space)
    (c : Fin 6 → ZMod 2) (hc : c ≠ 0) :
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

end SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroOrbitOriginalRows
