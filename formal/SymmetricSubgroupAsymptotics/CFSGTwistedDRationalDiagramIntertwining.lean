import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFieldTwist
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorExt

/-! The actual natural D representation intertwines the genuine diagram
automorphism of the original rational Serre quotient with the literal
coordinate-pair flip. This is proved on generators and their universal
quotient; injectivity of the representation is neither used nor claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRationalDiagramIntertwining
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalFork CFSGTwistedDNaturalFieldTwist CFSGSerreDiagram
open CFSG.Models.Chevalley

def flipLieHom (s : ℕ) : Mat ℚ (s + 2) →ₗ⁅ℚ⁆ Mat ℚ (s + 2) where
  __ := (flipAlgebra ℚ s).toLinearMap
  map_lie' := by
    intro x y
    change flipAlgebra ℚ s (x * y - y * x) =
      flipAlgebra ℚ s x * flipAlgebra ℚ s y - flipAlgebra ℚ s y * flipAlgebra ℚ s x
    simp only [map_sub, map_mul]

theorem cartan_all (s : ℕ) (i : Fin (s + 2)) :
    flipAlgebra ℚ s (cartan ℚ (s + 2) i) =
      cartan ℚ (s + 2) (CFSG.Models.dTwist i) := by
  simp only [cartan, Ring.lie_def, map_sub, map_mul, positive_all, negative_all]

theorem rational_intertwining (s : ℕ) (x : RationalLie (CartanMatrix.D (s + 4))) :
    flipAlgebra ℚ (s + 2) (rationalOrthogonalRepresentation (s + 4) (by omega) x) =
      rationalOrthogonalRepresentation (s + 4) (by omega)
        (rationalEquiv (CartanMatrix.D (s + 4)) (dPermutation (s + 4))
          (d_preserves (s + 4)) x) := by
  have he : (flipLieHom (s + 2)).comp (rationalOrthogonalRepresentation (s + 4) (by omega)) =
      (rationalOrthogonalRepresentation (s + 4) (by omega)).comp
        (rationalEquiv (CartanMatrix.D (s + 4)) (dPermutation (s + 4))
          (d_preserves (s + 4))).toLieHom := by
    apply CFSGSerreGeneratorExt.hom_ext
    intro g
    change flipAlgebra ℚ (s + 2)
      (rationalOrthogonalRepresentation (s + 4) (by omega)
        (generator (CartanMatrix.D (s + 4)) g)) =
      rationalOrthogonalRepresentation (s + 4) (by omega)
        (rationalEquiv (CartanMatrix.D (s + 4)) (dPermutation (s + 4))
          (d_preserves (s + 4)) (generator (CartanMatrix.D (s + 4)) g))
    rw [rationalEquiv_generator]
    cases g <;>
      simp only [nodeRename,
        rationalOrthogonalRepresentation_H, rationalOrthogonalRepresentation_E,
        rationalOrthogonalRepresentation_F, dPermutation_apply]
    · exact cartan_all (s + 2) _
    · exact positive_all ℚ (s + 2) _
    · exact negative_all ℚ (s + 2) _
  exact congrArg (fun f : RationalLie (CartanMatrix.D (s + 4)) →ₗ⁅ℚ⁆ Mat ℚ (s + 4) => f x) he

end SymmetricSubgroupAsymptotics.CFSGTwistedDRationalDiagramIntertwining
