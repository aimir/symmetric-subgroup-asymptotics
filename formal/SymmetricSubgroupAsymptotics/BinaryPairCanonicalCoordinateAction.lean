import SymmetricSubgroupAsymptotics.BinaryPairCanonicalPointCoordinates
import Mathlib.Data.Fintype.Pi

/-! The original point-function action is the literal canonical layer
matrix action after the SAME point labels. This requires neither a split
extension nor a choice of offsets. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance canonicalCoordinateActionFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem canonicalLayer_square_basis : ∀ i : Fin 16,
    binaryEightCanonicalLayerChange (binaryEightCanonicalLayerChange (Pi.single i 1))=
      Pi.single i 1 := by decide +kernel

theorem canonicalLayerChange_involutive (v : Fin 16 → ZMod 2) :
    binaryEightCanonicalLayerChange (binaryEightCanonicalLayerChange v)=v := by
  have he : binaryEightCanonicalLayerChange.comp binaryEightCanonicalLayerChange=LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c=c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply,mul_ite]
    simp only [LinearMap.comp_apply,hs,map_smul,canonicalLayer_square_basis,LinearMap.id_apply]
  exact DFunLike.congr_fun he v

def canonicalBinaryLayerAction (p : Equiv.Perm (Fin 16)) :
    (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
  binaryEightCanonicalLayerChange.comp
    (((binaryPermutationRepresentation 16) p).comp binaryEightCanonicalLayerChange)

namespace BinaryPairFrame
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (E : BinaryPairFrame U (Fin 8))

/-- Every original element, including arbitrary actual lift offsets, has
this exact canonical coordinate action. -/
theorem originalCoordinateRepresentation_canonical (t : U) :
    E.originalCoordinateRepresentation t=
      canonicalBinaryLayerAction (E.canonicalPointLabels.permCongrHom t.val) := by
  apply LinearMap.ext
  intro v
  obtain ⟨f,rfl⟩ := E.originalCoordinateEquiv.surjective v
  change E.originalCoordinateEquiv
      (fun x => (E.originalCoordinateEquiv.symm (E.originalCoordinateEquiv f)) ((t.val)⁻¹ x))=
        canonicalBinaryLayerAction _ (E.originalCoordinateEquiv f)
  rw [E.originalCoordinateEquiv.symm_apply_apply]
  rw [E.originalCoordinateEquiv_canonicalPointLabels,
    E.originalCoordinateEquiv_canonicalPointLabels]
  change binaryEightCanonicalLayerChange (fun j => f ((t.val)⁻¹ (E.canonicalPointLabels.symm j)))=
    binaryEightCanonicalLayerChange ((binaryPermutationRepresentation 16)
      (E.canonicalPointLabels.permCongrHom t.val)
        (binaryEightCanonicalLayerChange (binaryEightCanonicalLayerChange
          (fun j => f (E.canonicalPointLabels.symm j)))))
  rw [canonicalLayerChange_involutive]
  apply congrArg binaryEightCanonicalLayerChange
  funext j
  change f ((t.val)⁻¹ (E.canonicalPointLabels.symm j))=
    f (E.canonicalPointLabels.symm
      (E.canonicalPointLabels ((t.val)⁻¹ (E.canonicalPointLabels.symm j))))
  rw [Equiv.symm_apply_apply]

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
