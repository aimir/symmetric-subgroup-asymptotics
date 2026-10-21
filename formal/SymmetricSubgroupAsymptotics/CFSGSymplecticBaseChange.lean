import SymmetricSubgroupAsymptotics.CFSGSymplecticIntegralRepresentation
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixBaseChange
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice

/-! The genuine integral symplectic representation is base-changed on the
same source tensor product. Actual simple generator tensors map to the
literal standard symplectic matrices in every characteristic. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley

theorem integralRepresentation_H (r : ℕ) (i : Fin r) :
    integralSymplecticRepresentation r
      (CFSGSerreDiagram.latticeGenerator (CartanMatrix.C r).transpose
        (CartanMatrix.Generators.H i)) = cartan ℤ r i := by
  apply intMatrixLinearMap_injective r
  rw [integralSymplecticRepresentation_cast]
  change rationalSymplecticRepresentation r
    (generator (CartanMatrix.C r).transpose (CartanMatrix.Generators.H i)) =
      (Int.castRingHom ℚ).mapMatrix (cartan ℤ r i)
  rw [rationalSymplecticRepresentation_H, map_cartan]

theorem integralRepresentation_E (r : ℕ) (i : Fin r) :
    integralSymplecticRepresentation r
      (CFSGSerreDiagram.latticeGenerator (CartanMatrix.C r).transpose
        (CartanMatrix.Generators.E i)) = positive ℤ r i := by
  apply intMatrixLinearMap_injective r
  rw [integralSymplecticRepresentation_cast]
  change rationalSymplecticRepresentation r
    (generator (CartanMatrix.C r).transpose (CartanMatrix.Generators.E i)) =
      (Int.castRingHom ℚ).mapMatrix (positive ℤ r i)
  rw [rationalSymplecticRepresentation_E, map_positive]

theorem integralRepresentation_F (r : ℕ) (i : Fin r) :
    integralSymplecticRepresentation r
      (CFSGSerreDiagram.latticeGenerator (CartanMatrix.C r).transpose
        (CartanMatrix.Generators.F i)) = negative ℤ r i := by
  apply intMatrixLinearMap_injective r
  rw [integralSymplecticRepresentation_cast]
  change rationalSymplecticRepresentation r
    (generator (CartanMatrix.C r).transpose (CartanMatrix.Generators.F i)) =
      (Int.castRingHom ℚ).mapMatrix (negative ℤ r i)
  rw [rationalSymplecticRepresentation_F, map_negative]

def symplecticBaseChange (K : Type*) [CommRing K] (r : ℕ) :
    (K ⊗[ℤ] integralLattice (CartanMatrix.C r).transpose) →ₗ[K] Mat K r :=
  (CFSGIntegerMatrixBaseChange.tensorMap K (Index r)).comp
    ((integralSymplecticRepresentation r).baseChange K)

theorem symplecticBaseChange_tmul (K : Type*) [CommRing K] (r : ℕ)
    (a : K) (x : integralLattice (CartanMatrix.C r).transpose) :
    symplecticBaseChange K r (a ⊗ₜ[ℤ] x) =
      a • (Int.castRingHom K).mapMatrix (integralSymplecticRepresentation r x) := by
  rw [symplecticBaseChange, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    CFSGIntegerMatrixBaseChange.tensorMap_tmul]
  rfl

theorem symplecticBaseChange_H (K : Type*) [CommRing K] (r : ℕ) (i : Fin r) :
    symplecticBaseChange K r (1 ⊗ₜ[ℤ]
      CFSGSerreDiagram.latticeGenerator (CartanMatrix.C r).transpose
        (CartanMatrix.Generators.H i)) = cartan K r i := by
  rw [symplecticBaseChange_tmul, integralRepresentation_H, one_smul, map_cartan]

theorem symplecticBaseChange_E (K : Type*) [CommRing K] (r : ℕ) (i : Fin r) :
    symplecticBaseChange K r (1 ⊗ₜ[ℤ]
      CFSGSerreDiagram.latticeGenerator (CartanMatrix.C r).transpose
        (CartanMatrix.Generators.E i)) = positive K r i := by
  rw [symplecticBaseChange_tmul, integralRepresentation_E, one_smul, map_positive]

theorem symplecticBaseChange_F (K : Type*) [CommRing K] (r : ℕ) (i : Fin r) :
    symplecticBaseChange K r (1 ⊗ₜ[ℤ]
      CFSGSerreDiagram.latticeGenerator (CartanMatrix.C r).transpose
        (CartanMatrix.Generators.F i)) = negative K r i := by
  rw [symplecticBaseChange_tmul, integralRepresentation_F, one_smul, map_negative]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
