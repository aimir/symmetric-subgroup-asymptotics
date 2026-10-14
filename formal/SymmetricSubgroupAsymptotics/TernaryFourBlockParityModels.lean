import SymmetricSubgroupAsymptotics.TernaryParitySignModel

/-! Concrete four-block parity labels and the two actual signed
complements. The common-sign projection and independent-sign action share
the same source normal-generator theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace TernaryFourBlockParityModels

open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block)
open BinaryPermutationSemidirectNormalGenerators

def label (i : Block) : Fin 2 := ⟨i.toAdd.val % 2, Nat.mod_lt _ (by decide)⟩

def cyclicBlockAction : Block →* Equiv.Perm Block := MulAction.toPermHom Block Block

theorem cyclic_label (g i : Block) :
    label (cyclicBlockAction g i) = cyclicLabels g (label i) := by
  revert g i
  decide +kernel

theorem dihedral_label (g : TernaryFourBlockMetacyclicModel.Complement true) (i : Block) :
    label (TernaryFourBlockMetacyclicModel.blockAction true g i) =
      dihedralLabels g (label i) := by
  revert g i
  decide +kernel

def sumProjection : Vector →ₗ[ZMod 2] Vector where
  toFun v _ := ∑ i : Fin 2, v i
  map_add' := by intro v w; funext i; exact Finset.sum_add_distrib
  map_smul' := by
    intro a v
    funext i
    simp only [Pi.smul_apply, ← Finset.smul_sum, RingHom.id_apply]

theorem sumProjection_equivariant {R : Type} [Group R]
    (p : R →* Equiv.Perm (Fin 2)) (g : R) (v : Vector) :
    sumProjection (linearAction p g v) = linearAction p g (sumProjection v) := by
  funext i
  change (∑ j : Fin 2, v (p g⁻¹ j)) = ∑ j : Fin 2, v j
  exact Fintype.sum_equiv (p g⁻¹) (fun j : Fin 2 ↦ v (p g⁻¹ j)) v (fun _ ↦ rfl)

def cyclicAction :=
  TernaryParitySignModel.linearAction cyclicLabels cyclicBlockAction label cyclic_label
    (LinearMap.id : Vector →ₗ[ZMod 2] Vector) (fun _ _ ↦ rfl)

def dihedralAction (q : Vector →ₗ[ZMod 2] Vector)
    (hq : ∀ g v, q (linearAction dihedralLabels g v) = linearAction dihedralLabels g (q v)) :=
  TernaryParitySignModel.linearAction dihedralLabels
    (TernaryFourBlockMetacyclicModel.blockAction true) label dihedral_label q hq

def commonDihedralAction := dihedralAction sumProjection (sumProjection_equivariant dihedralLabels)
def parityDihedralAction := dihedralAction LinearMap.id (fun _ _ ↦ rfl)

theorem cyclic_representation_comp :
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation cyclicAction).comp
        (SemidirectProduct.inr : Block →* CyclicModel) =
      permutationFunctionRepresentation (ZMod 3) Block Block := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  funext i
  exact TernaryParitySignModel.linearAction_inr cyclicLabels cyclicBlockAction
    label cyclic_label LinearMap.id (fun _ _ ↦ rfl) g v i

theorem dihedral_representation_comp (q : Vector →ₗ[ZMod 2] Vector)
    (hq : ∀ g v, q (linearAction dihedralLabels g v) = linearAction dihedralLabels g (q v)) :
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation (dihedralAction q hq)).comp
        ((SemidirectProduct.inr : TernaryFourBlockMetacyclicModel.Complement true →* DihedralModel).comp
          (SemidirectProduct.inl : Block →* TernaryFourBlockMetacyclicModel.Complement true)) =
      permutationFunctionRepresentation (ZMod 3) Block Block := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  funext i
  change TernaryParitySignModel.linearAction dihedralLabels
    (TernaryFourBlockMetacyclicModel.blockAction true) label dihedral_label q hq
      (SemidirectProduct.inr (SemidirectProduct.inl g)) v i = v (g⁻¹ * i)
  rw [TernaryParitySignModel.linearAction_inr]
  simp [TernaryFourBlockMetacyclicModel.blockAction, TernaryFourBlockMetacyclicModel.bitAction]

private theorem regular_generated :
    RepresentationGeneratedBy (permutationFunctionRepresentation (ZMod 3) Block Block) 1 := by
  apply permutationFunctionRepresentation_generatedBy_orbitCover (fun _ : Fin 1 ↦ 1)
  intro c
  exact ⟨0, c, mul_one c⟩

theorem cyclic_generated :
    RepresentationGeneratedBy (LinearSemidirectCoprimeSocleBounds.linearRepresentation cyclicAction) 1 := by
  apply RepresentationGeneratedBy.of_comp _ (SemidirectProduct.inr : Block →* CyclicModel)
  rw [cyclic_representation_comp]
  exact regular_generated

theorem dihedral_generated (q : Vector →ₗ[ZMod 2] Vector)
    (hq : ∀ g v, q (linearAction dihedralLabels g v) = linearAction dihedralLabels g (q v)) :
    RepresentationGeneratedBy
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation (dihedralAction q hq)) 1 := by
  apply RepresentationGeneratedBy.of_comp _
    ((SemidirectProduct.inr : TernaryFourBlockMetacyclicModel.Complement true →* DihedralModel).comp
      (SemidirectProduct.inl : Block →* TernaryFourBlockMetacyclicModel.Complement true))
  rw [dihedral_representation_comp]
  exact regular_generated

theorem cyclic_socle_of_surjective {Q : Type} [Group Q]
    (pi : LinearSemidirectCoprimeSocleBounds.Model cyclicAction →* Q)
    (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 2 :=
  LinearSemidirectCoprimeQuotientSocles.socle_of_surjective cyclicAction
    (by rw [cyclic_card]; decide) 1 2 cyclic_generated cyclic_normalGen pi hpi

theorem dihedral_socle_of_surjective (q : Vector →ₗ[ZMod 2] Vector)
    (hq : ∀ g v, q (linearAction dihedralLabels g v) = linearAction dihedralLabels g (q v))
    {Q : Type} [Group Q]
    (pi : LinearSemidirectCoprimeSocleBounds.Model (dihedralAction q hq) →* Q)
    (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 3 :=
  LinearSemidirectCoprimeQuotientSocles.socle_of_surjective (dihedralAction q hq)
    (by rw [dihedral_card]; decide) 1 3 (dihedral_generated q hq) dihedral_normalGen pi hpi

end TernaryFourBlockParityModels
end SymmetricSubgroupAsymptotics

end
