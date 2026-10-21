import SymmetricSubgroupAsymptotics.BinaryPairOriginalRadicalDisplacements
import SymmetricSubgroupAsymptotics.IntrinsicRadicalIndexTwoOrbitWitnessKernel

/-! Original pair coordinates retain the whole radical when applying the
three-orbit-image argument to the SAME actual index-two subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin w))

theorem kernel_le_of_original_intrinsic_radical_three_orbit_witnesses
    {C : Type*} [AddCommGroup C] [Module (ZMod 2) C]
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (S R : Submodule (ZMod 2) (Fin (w+w) → ZMod 2))
    (hS : (E.originalCoordinateSubrepresentation W).toSubmodule = S)
    (hR : ((Representation.Coinvariants.ker W.toRepresentation).map
      W.toSubmodule.subtype).map E.originalCoordinateEquiv.toLinearMap = R)
    (projection : (Fin (w+w) → ZMod 2) →ₗ[ZMod 2] C)
    (sectionMap : C →ₗ[ZMod 2] (Fin (w+w) → ZMod 2))
    (hdefect : ∀ v, v - sectionMap (projection v) ∈ S)
    (hwitness : ∀ c : C, c ≠ 0 → ∃ u : Fin 3 → U,
      ∀ i j : Fin 3, i ≠ j →
        E.originalCoordinateRepresentation (u i) (sectionMap c) -
          E.originalCoordinateRepresentation (u j) (sectionMap c) ∉ R)
    (D : Subgroup U) (hindex : D.index = 2)
    (K : Submodule (ZMod 2) (Fin (w+w) → ZMod 2))
    (hfixed : ∀ d : D, ∀ v ∈ K,
      E.originalCoordinateRepresentation (d : U) v - v ∈ R) : K ≤ S := by
  have hr : (Representation.Coinvariants.ker
      (E.originalCoordinateSubrepresentation W).toRepresentation).map
        (E.originalCoordinateSubrepresentation W).toSubmodule.subtype = R :=
    (RepresentationCoordinateChange.subrepresentation_radical
      (permutationFunctionRepresentation (ZMod 2) U X) E.originalCoordinateEquiv W).symm.trans hR
  exact submodule_le_of_intrinsic_radical_three_orbit_witnesses_index_two
    E.originalCoordinateRepresentation (E.originalCoordinateSubrepresentation W)
    S R hS hr projection sectionMap hdefect hwitness D hindex K hfixed

end SymmetricSubgroupAsymptotics.BinaryPairFrame
