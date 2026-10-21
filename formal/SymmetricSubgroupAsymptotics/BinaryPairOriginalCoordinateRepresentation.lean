import SymmetricSubgroupAsymptotics.RepresentationCoordinateChangeCoinvariants
import SymmetricSubgroupAsymptotics.BinarySplitAffineFunctionCoordinates

/-! Reversible coordinates and literal affine rows for the same original
point-function module. Every row used below is an element of the original
source, obtained from a proved equality with its full zero model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w))

def originalCoordinateEquiv : (X → ZMod 2) ≃ₗ[ZMod 2] (Fin (w+w) → ZMod 2) :=
  F.pairLayerCoordinateEquiv.trans pairLayerFlatten

def originalCoordinateRepresentation : Representation (ZMod 2) U (Fin (w+w) → ZMod 2) :=
  RepresentationCoordinateChange.action
    (permutationFunctionRepresentation (ZMod 2) U X) F.originalCoordinateEquiv

def originalCoordinateSubrepresentation
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Subrepresentation F.originalCoordinateRepresentation :=
  RepresentationCoordinateChange.subrepresentation
    (permutationFunctionRepresentation (ZMod 2) U X) F.originalCoordinateEquiv W

theorem originalCoordinateSubrepresentation_head
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants =
      Module.finrank (ZMod 2) (F.originalCoordinateSubrepresentation W).toRepresentation.Coinvariants :=
  RepresentationCoordinateChange.subrepresentation_head _ _ W

theorem mem_originalCoordinateSubrepresentation_iff
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (v : Fin (w+w) → ZMod 2) :
    v ∈ (F.originalCoordinateSubrepresentation W).toSubmodule ↔
      F.originalCoordinateEquiv.symm v ∈ W.toSubmodule :=
  RepresentationCoordinateChange.mem_subrepresentation_iff _ _ W v

/-- Each full zero-model coordinate row belongs to the same original
permutation subgroup. -/
def originalZeroRow (hzero : U = F.splitAffineAction)
    (t : F.top.range) (a : Fin w → ZMod 2) (ha : a ∈ F.kernelSpace) : U :=
  ⟨F.affinePermutation t.val a, by
    have hm : F.affinePermutation t.val a ∈ F.splitAffineAction :=
      Subgroup.subset_closure ⟨t,a,ha,rfl⟩
    exact Eq.mpr (congrArg
      (fun C : Subgroup (Equiv.Perm X) => F.affinePermutation t.val a ∈ C) hzero) hm⟩

/-- The coordinate action of an original row is the literal affine action
used by the sparse certificates, with no lost original lift offsets. -/
theorem originalCoordinateRepresentation_zeroRow
    (hzero : U = F.splitAffineAction)
    (t : F.top.range) (a : Fin w → ZMod 2) (ha : a ∈ F.kernelSpace) :
    F.originalCoordinateRepresentation (F.originalZeroRow hzero t a ha) =
      pairLayerFlatten.toLinearMap.comp
        ((affinePairLayerMap t.val a).comp pairLayerFlatten.symm.toLinearMap) := by
  apply LinearMap.ext
  intro v
  change F.originalCoordinateEquiv
      (fun x => (F.originalCoordinateEquiv.symm v)
        ((F.affinePermutation t.val a)⁻¹ x)) = _
  change pairLayerFlatten
      (F.pairLayerCoordinateEquiv
        (fun x => (F.originalCoordinateEquiv.symm v)
          ((F.affinePermutation t.val a)⁻¹ x))) = _
  rw [F.pairLayerCoordinateEquiv_affine_action]
  change pairLayerFlatten (affinePairLayerMap t.val a
    (F.pairLayerCoordinateEquiv
      (F.pairLayerCoordinateEquiv.symm (pairLayerFlatten.symm v)))) = _
  rw [F.pairLayerCoordinateEquiv.apply_symm_apply]
  rfl

end SymmetricSubgroupAsymptotics.BinaryPairFrame
