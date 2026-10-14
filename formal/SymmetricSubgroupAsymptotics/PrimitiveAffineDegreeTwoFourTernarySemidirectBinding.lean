import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryCoreCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryCoreWords

/-!
# Exact semidirect binding of the eight original tops

Four prescribed conjugates of the translation generator span each core.
The binary complement has explicit words in the original nontranslation
generators. These two word calculations identify the range of the compact
semidirect model with the actual literal generator closure, without an order
comparison or an enumeration of the top group.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoFourTernarySemidirectBinding

open TernarySignedBlockCoordinates
open PrimitiveAffineDegreeTwoFourTernaryCoordinates
open PrimitiveAffineDegreeTwoFourTernaryBinaryCoordinates
open PrimitiveAffineDegreeTwoFourTernaryCoreCoordinates
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def basisVector : Fin 8 → Fin 4 → Vector :=
  let paired := ![![0, 1, 0, 1], ![1, 0, 1, 0], ![0, 1, 0, 1], ![1, 0, 1, 0]]
  let aug := ![![0, 1, 1, 1], ![1, 0, 1, 1], ![1, 1, 0, 1], ![1, 1, 1, 0]]
  let full := ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0]]
  let twisted := ![![0, 0, 0, 1], ![0, 2, 0, 0], ![1, 0, 0, 0], ![0, 0, 2, 0]]
  ![paired, paired, aug, full, full, twisted, full, full]

def coefficientMap : Fin 8 → Vector →ₗ[Scalar] Vector :=
  let a : Vector →ₗ[Scalar] Scalar := LinearMap.proj 0
  let b : Vector →ₗ[Scalar] Scalar := LinearMap.proj 1
  let c : Vector →ₗ[Scalar] Scalar := LinearMap.proj 2
  let d : Vector →ₗ[Scalar] Scalar := LinearMap.proj 3
  let paired := LinearMap.pi ![b, a, 0, 0]
  let aug := LinearMap.pi ![-(a + b + c) - a, -(a + b + c) - b,
    -(a + b + c) - c, 0]
  let full := LinearMap.pi ![d, c, b, a]
  let twisted := LinearMap.pi ![d, (2 : Scalar) • b, a, (2 : Scalar) • c]
  ![paired, paired, aug, full, full, twisted, full, full]

def basisMap (r : Fin 8) : Vector →ₗ[Scalar] Vector :=
  (LinearMap.proj 0).smulRight (basisVector r 0) +
    (LinearMap.proj 1).smulRight (basisVector r 1) +
    (LinearMap.proj 2).smulRight (basisVector r 2) +
    (LinearMap.proj 3).smulRight (basisVector r 3)

theorem basis_factorization (r : Fin 8) :
    (basisMap r).comp (coefficientMap r) = projection r := by
  apply LinearMap.pi_ext
  intro i c
  funext j
  fin_cases r <;> revert i c j <;> decide +kernel

def coordinateConjugator (r : Fin 8) : Fin 4 → Affine :=
  ![1, generators r (PrimitiveAffineDegreeTwoFourTernaryCoreWords.firstBlockLetter r),
    generators r (PrimitiveAffineDegreeTwoFourTernaryCoreWords.secondBlockLetter r),
    generators r (PrimitiveAffineDegreeTwoFourTernaryCoreWords.firstBlockLetter r) *
      generators r (PrimitiveAffineDegreeTwoFourTernaryCoreWords.secondBlockLetter r)]

theorem basis_translation_word (r : Fin 8) (i : Fin 4) :
    TernarySignedBlockCoordinates.translate (basisVector r i) =
      coordinateConjugator r i * generators r 0 * (coordinateConjugator r i)⁻¹ := by
  apply action_injective
  apply Equiv.ext
  intro p
  fin_cases r <;> fin_cases i <;> revert p <;> decide +kernel

theorem coordinate_generator_mem (r : Fin 8) (j : Fin 5) :
    generators r j ∈ CoordinateTop r := Subgroup.subset_closure (Set.mem_range_self j)

theorem coordinateConjugator_mem (r : Fin 8) (i : Fin 4) :
    coordinateConjugator r i ∈ CoordinateTop r := by
  fin_cases i
  · exact Subgroup.one_mem _
  · exact coordinate_generator_mem r _
  · exact coordinate_generator_mem r _
  · exact Subgroup.mul_mem _ (coordinate_generator_mem r _) (coordinate_generator_mem r _)

theorem basis_translation_mem (r : Fin 8) (i : Fin 4) :
    TernarySignedBlockCoordinates.translate (basisVector r i) ∈ CoordinateTop r := by
  rw [basis_translation_word]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (coordinateConjugator_mem r i) (coordinate_generator_mem r 0))
    (Subgroup.inv_mem _ (coordinateConjugator_mem r i))

def translationGroup (H : Subgroup Affine) : AddSubgroup Vector where
  carrier := fun v => TernarySignedBlockCoordinates.translate v ∈ H
  zero_mem' := H.one_mem
  add_mem' := by
    intro v w hv hw
    change TernarySignedBlockCoordinates.translate (v + w) ∈ H
    rw [← translate_mul]
    exact H.mul_mem hv hw
  neg_mem' := by
    intro v hv
    change SemidirectProduct.inl ((Multiplicative.ofAdd v)⁻¹) ∈ H
    rw [map_inv]
    exact H.inv_mem hv

def translationSpace (H : Subgroup Affine) : Submodule Scalar Vector where
  toAddSubmonoid := (translationGroup H).toAddSubmonoid
  smul_mem' := fun c _ hv => zmod_smul_mem (K := translationGroup H) hv c

theorem core_translation_mem (r : Fin 8) (v : Core r) :
    TernarySignedBlockCoordinates.translate v.val ∈ CoordinateTop r := by
  let S := translationSpace (CoordinateTop r)
  have hb (i : Fin 4) : basisVector r i ∈ S := basis_translation_mem r i
  have he : basisMap r (coefficientMap r v.val) = v.val :=
    (congrArg (fun f : Vector →ₗ[Scalar] Vector => f v.val)
      (basis_factorization r)).trans v.property
  change v.val ∈ S
  rw [← he]
  exact S.add_mem
    (S.add_mem
      (S.add_mem (S.smul_mem _ (hb 0)) (S.smul_mem _ (hb 1)))
      (S.smul_mem _ (hb 2)))
    (S.smul_mem _ (hb 3))

theorem signed_generator_eq (r : Fin 8) (j : Fin 5) :
    signed (toSigned (frameGenerators r j)) = if j = 0 then 1 else generators r j := by
  apply action_injective
  apply Equiv.ext
  intro p
  fin_cases r <;> fin_cases j <;> revert p <;> decide +kernel

theorem signed_generator_mem (r : Fin 8) (j : Fin 5) :
    signed (toSigned (frameGenerators r j)) ∈ CoordinateTop r := by
  rw [signed_generator_eq]
  split
  · exact Subgroup.one_mem _
  · exact coordinate_generator_mem r j

theorem complement_signed_mem (r : Fin 8) (q : Complement r) :
    signed (toSigned q.val) ∈ CoordinateTop r := by
  let f : Frame →* Affine := SemidirectProduct.inr.comp toSigned
  have h : Subgroup.closure (Set.range (frameGenerators r)) ≤ (CoordinateTop r).comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact signed_generator_mem r j
  apply h
  rw [← complement_eq_closure]
  exact q.property

theorem generator_core_mem (r : Fin 8) (j : Fin 5) :
    (generators r j).left.toAdd ∈ Core r := by
  change projection r (generators r j).left.toAdd = (generators r j).left.toAdd
  funext i
  fin_cases r <;> fin_cases j <;> revert i <;> decide +kernel

theorem modelInclusion_range (r : Fin 8) :
    (modelInclusion r).range = CoordinateTop r := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rw [← SemidirectProduct.inl_left_mul_inr_right (modelInclusion r g)]
    exact Subgroup.mul_mem _ (core_translation_mem r g.left.toAdd)
      (complement_signed_mem r g.right)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨⟨Multiplicative.ofAdd ⟨(generators r j).left.toAdd,
      generator_core_mem r j⟩, ⟨frameGenerators r j, frameGenerators_mem r j⟩⟩, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact frameGenerators_binding r j

noncomputable def modelOriginalEquiv (r : Fin 8) :
    Model r ≃* (degreeTwoFourTernaryInterface r).top :=
  ((MonoidHom.ofInjective (modelInclusion_injective r)).trans
    (MulEquiv.subgroupCongr (modelInclusion_range r))).trans (originalEquiv r)

theorem modelOriginalEquiv_apply (r : Fin 8) (g : Model r) :
    (modelOriginalEquiv r g : Equiv.Perm (Fin 12)) =
      literalAction (phase r) (modelInclusion r g) := rfl

noncomputable def affineEquiv (r : Fin 8) :
    (degreeTwoFourTernaryInterface r).top ≃* Model r := (modelOriginalEquiv r).symm

end PrimitiveAffineDegreeTwoFourTernarySemidirectBinding
end SymmetricSubgroupAsymptotics

end
