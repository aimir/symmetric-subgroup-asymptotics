import SymmetricSubgroupAsymptotics.CFSGTwistedDImageTwist
import SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagramCovariance
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDImageRealization

/-! The SAME original D model action and the actual matrix-image twist
intertwine on every image vector. Thus original fixed elements commute
with the image twist, without asserting fixed literal natural lifts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDModelImageCovariance
open CFSG.Models.Chevalley CFSGOrthogonalDSerreMatrices CFSGSerreDiagram
open CFSGTwistedDImageTwist CFSGTwistedDNaturalFieldTwist CFSGTwistedDFieldDiagramIntertwining
variable (K : Type) [Field K]

theorem rangeTwist_baseChange (s : ℕ) (σ : K ≃+* K)
    (x : Space (CartanMatrix.D (s + 4)) K) :
    rangeTwist K s σ ((orthogonalBaseChange K (s + 4) (by omega)).rangeRestrict x) =
      (orthogonalBaseChange K (s + 4) (by omega)).rangeRestrict
        (spaceEquiv (CartanMatrix.D (s + 4)) K (dPermutation (s + 4)) (d_preserves (s + 4))
          (CFSGSerreField.semilinearEquiv (CartanMatrix.D (s + 4)) K σ x)) := by
  apply Subtype.ext
  exact (baseChange_field_diagram K s σ x).symm

theorem image_covariance (s : ℕ) (σ : K ≃+* K)
    (g : Model (CartanMatrix.D (s + 4)) K)
    (y : (orthogonalBaseChange K (s + 4) (by omega)).range) :
    orthogonalImageRepresentation K (s + 4) (by omega)
      (CFSGSerreFieldDiagram.modelAutomorphism (CartanMatrix.D (s + 4)) K
        (dPermutation (s + 4)) (d_preserves (s + 4)) σ g) (rangeTwist K s σ y) =
      rangeTwist K s σ (orthogonalImageRepresentation K (s + 4) (by omega) g y) := by
  obtain ⟨x, rfl⟩ := (orthogonalBaseChange K (s + 4) (by omega)).surjective_rangeRestrict y
  rw [rangeTwist_baseChange]
  apply Subtype.ext
  change (orthogonalImageRepresentation K (s + 4) (by omega)
    (CFSGSerreFieldDiagram.modelAutomorphism (CartanMatrix.D (s + 4)) K
      (dPermutation (s + 4)) (d_preserves (s + 4)) σ g)
    ((orthogonalBaseChange K (s + 4) (by omega)).rangeRestrict
      (spaceEquiv (CartanMatrix.D (s + 4)) K (dPermutation (s + 4)) (d_preserves (s + 4))
        (CFSGSerreField.semilinearEquiv (CartanMatrix.D (s + 4)) K σ x)))).val =
    matrixTwist K (s + 2) σ
      ((orthogonalImageRepresentation K (s + 4) (by omega) g
        ((orthogonalBaseChange K (s + 4) (by omega)).rangeRestrict x)).val)
  rw [CFSGSerreSquareZeroMatrix.imageRepresentation_intertwines,
    CFSGSerreSquareZeroMatrix.imageRepresentation_intertwines,
    CFSGSerreFieldDiagramCovariance.model_covariance, baseChange_field_diagram]

theorem fixed_image_commutes (s : ℕ) (σ : K ≃+* K)
    (g : Model (CartanMatrix.D (s + 4)) K)
    (hg : CFSGSerreFieldDiagram.modelAutomorphism (CartanMatrix.D (s + 4)) K
      (dPermutation (s + 4)) (d_preserves (s + 4)) σ g = g)
    (y : (orthogonalBaseChange K (s + 4) (by omega)).range) :
    orthogonalImageRepresentation K (s + 4) (by omega) g (rangeTwist K s σ y) =
      rangeTwist K s σ (orthogonalImageRepresentation K (s + 4) (by omega) g y) := by
  simpa only [hg] using image_covariance K s σ g y

end SymmetricSubgroupAsymptotics.CFSGTwistedDModelImageCovariance
