import SymmetricSubgroupAsymptotics.QuaternaryPauliFourierPhaseNormalization
import SymmetricSubgroupAsymptotics.TernaryHeisenbergCompatibleNormalizerIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticFullGroup
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryProjectiveEquiv

/-! The actual Pauli27 and its actual Fourier/phase normalizers survive
in the FULL elementary-projective symplectic quotient. Scalar extension
from F2 is injective; in characteristic two the proved elementary centre
is trivial. No normalizer order, splitting or model-recognition premise
occurs in the final proper-index statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPauliPrimeIndex
open CFSGSymplecticSerreMatrices CFSGSymplecticStabilizerCoordinates

variable (K : Type) [Field K] [CharP K 2]

private def binarySymplecticHom : Matrix.symplecticGroup (Fin 3) (ZMod 2) →*
    Matrix.symplecticGroup (Fin 3) K := by
  let φ : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hJ : (Matrix.J (Fin 3) (ZMod 2)).map φ=Matrix.J (Fin 3) K := by
    rw [Matrix.J,Matrix.J,Matrix.fromBlocks_map]
    congr 1
    · exact map_zero φ.mapMatrix
    · simpa only [map_one] using map_neg φ.mapMatrix (1:Matrix (Fin 3) (Fin 3) (ZMod 2))
    · exact map_one φ.mapMatrix
    · exact map_zero φ.mapMatrix
  exact
    { toFun := fun A => ⟨A.val.map φ,by
        apply _root_.SymplecticGroup.mem_iff.mpr
        have he := congrArg φ.mapMatrix (_root_.SymplecticGroup.mem_iff.mp A.property)
        change φ.mapMatrix (A.val*Matrix.J (Fin 3) (ZMod 2)*A.val.transpose)=
          φ.mapMatrix (Matrix.J (Fin 3) (ZMod 2)) at he
        simpa only [map_mul,RingHom.mapMatrix_apply,Matrix.transpose_map,hJ] using he⟩
      map_one' := Subtype.ext (map_one φ.mapMatrix)
      map_mul' A C := Subtype.ext (map_mul φ.mapMatrix A.val C.val) }

private theorem binarySymplecticHom_injective : Function.Injective (binarySymplecticHom K) := by
  intro A C he
  apply Subtype.ext
  funext i j
  exact (ZMod.castHom (dvd_refl 2) K).injective
    (congrFun (congrFun (congrArg Subtype.val he) i) j)

private def projectiveHom :
    QuaternaryUnitarySymplecticEmbedding.unitary (ZMod 3) →* elementaryProjective K 3 :=
  (binaryProjectiveEquiv K 2).toMonoidHom.comp
    ((elementarySymplecticEquiv K 3).symm.toMonoidHom.comp
      ((binarySymplecticHom K).comp (QuaternaryUnitarySymplecticEmbedding.symplecticHom (ZMod 3))))

private theorem projectiveHom_injective : Function.Injective (projectiveHom K) :=
  (binaryProjectiveEquiv K 2).injective.comp
    ((elementarySymplecticEquiv K 3).symm.injective.comp
      ((binarySymplecticHom_injective K).comp
        (QuaternaryUnitarySymplecticEmbedding.symplecticHom_injective (ZMod 3))))

private theorem map_conjugacy {A B : Type*} [Group A] [Group B]
    (f : A →* B) (x y z : A) (h : x*y*x⁻¹=z) : f x*f y*(f x)⁻¹=f z := by
  simpa only [map_mul,map_inv] using congrArg f h

/-- The literal elementary projective rank-three group over ANY finite
characteristic-two field has the same actual 3-local index27 obstruction. -/
theorem projective_proper_index_ge_twentySeven [Finite K]
    [IsSimpleGroup (elementaryProjective K 3)]
    (H : Subgroup (elementaryProjective K 3)) (hH : H≠⊤) : 27 ≤ H.index := by
  letI : Finite (elementaryProjective K 3) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K 3)))
      (QuotientGroup.mk'_surjective _)
  let f := (projectiveHom K).comp QuaternaryPauliUnitaryRepresentation.representation
  have hf : Function.Injective f := (projectiveHom_injective K).comp
    QuaternaryPauliUnitaryRepresentation.representation_injective
  apply TernaryHeisenbergCompatibleNormalizerIndex.proper_index_ge_twentySeven f hf
    (projectiveHom K QuaternaryPauliUnitaryRepresentation.fourier)
    (projectiveHom K QuaternaryPauliUnitaryRepresentation.phase)
    QuaternaryPauliFourierPhaseNormalization.rotation
    QuaternaryPauliFourierPhaseNormalization.shear ?_ ?_
    QuaternaryPauliFourierPhaseNormalization.rotation_coordinates
    QuaternaryPauliFourierPhaseNormalization.shear_coordinates H hH
  · intro h
    exact map_conjugacy (projectiveHom K) _ _ _
      (QuaternaryPauliFourierPhaseNormalization.fourier_normalizes h)
  · intro h
    exact map_conjugacy (projectiveHom K) _ _ _
      (QuaternaryPauliFourierPhaseNormalization.phase_normalizes h)

end SymmetricSubgroupAsymptotics.CFSGSymplecticPauliPrimeIndex
