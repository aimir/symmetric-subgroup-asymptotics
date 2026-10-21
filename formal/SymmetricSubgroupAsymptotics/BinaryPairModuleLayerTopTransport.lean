import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerHead
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantSurjectiveGroup

/-! Pair-module layers descend through the actual onto top map without
changing their underlying vectors or their intrinsic coinvariant radical.
Literal top-model equality then changes only the acting subgroup type. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w))

def descendPairLayer (A : Subrepresentation F.pulledBackCoordinateTopAction) :
    Subrepresentation F.coordinateTopAction where
  toSubmodule := A.toSubmodule
  apply_mem_toSubmodule t v hv := by
    obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
    exact A.apply_mem_toSubmodule u hv

theorem descendPairLayer_representation (A : Subrepresentation F.pulledBackCoordinateTopAction) :
    A.toRepresentation = (F.descendPairLayer A).toRepresentation.comp F.top.rangeRestrict := by
  ext u v
  rfl

theorem descendPairLayer_radical (A : Subrepresentation F.pulledBackCoordinateTopAction) :
    Representation.Coinvariants.ker A.toRepresentation =
      Representation.Coinvariants.ker (F.descendPairLayer A).toRepresentation := by
  rw [F.descendPairLayer_representation A]
  exact coinvariants_ker_comp_surjective_group _ F.top.rangeRestrict F.top.rangeRestrict_surjective

theorem descendPairLayer_head (A : Subrepresentation F.pulledBackCoordinateTopAction) :
    Module.finrank (ZMod 2) A.toRepresentation.Coinvariants =
      Module.finrank (ZMod 2) (F.descendPairLayer A).toRepresentation.Coinvariants := by
  rw [F.descendPairLayer_representation A]
  exact coinvariants_finrank_comp_surjective_group _ F.top.rangeRestrict F.top.rangeRestrict_surjective

def literalPairLayer (H : Subgroup (Equiv.Perm (Fin w))) (hH : F.top.range = H)
    (A : Subrepresentation F.pulledBackCoordinateTopAction) :
    Subrepresentation ((binaryPermutationRepresentation w).comp H.subtype) := by
  subst H
  exact F.descendPairLayer A

theorem literalPairLayer_space
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : F.top.range = H)
    (A : Subrepresentation F.pulledBackCoordinateTopAction) :
    (F.literalPairLayer H hH A).toSubmodule = A.toSubmodule := by
  subst H
  rfl

theorem literalPairLayer_radical
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : F.top.range = H)
    (A : Subrepresentation F.pulledBackCoordinateTopAction) :
    (Representation.Coinvariants.ker (F.literalPairLayer H hH A).toRepresentation).map
        (F.literalPairLayer H hH A).toSubmodule.subtype =
      (Representation.Coinvariants.ker A.toRepresentation).map A.toSubmodule.subtype := by
  subst H
  rw [F.descendPairLayer_radical A]
  rfl

theorem literalPairLayer_head
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : F.top.range = H)
    (A : Subrepresentation F.pulledBackCoordinateTopAction) :
    Module.finrank (ZMod 2) (F.literalPairLayer H hH A).toRepresentation.Coinvariants =
      Module.finrank (ZMod 2) A.toRepresentation.Coinvariants := by
  subst H
  exact (F.descendPairLayer_head A).symm

end SymmetricSubgroupAsymptotics.BinaryPairFrame
