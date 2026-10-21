import SymmetricSubgroupAsymptotics.CFSGSymplecticBaseChange
import SymmetricSubgroupAsymptotics.CFSGSymplecticRootCentralizer

/-! The actual integral symplectic representation image has scalar
commutant. It suffices that the image contains the genuine simple E/F
matrices; no assertion that the image is the whole classical Lie algebra
is needed. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley

theorem symplecticImage_centralizer (K : Type*) [CommRing K] (r : ℕ)
    (A : Mat K (r + 1))
    (hA : ∀ x : K ⊗[ℤ] integralLattice (CartanMatrix.C (r + 1)).transpose,
      A * symplecticBaseChange K (r + 1) x = symplecticBaseChange K (r + 1) x * A) :
    ∃ c : K, A = c • (1 : Mat K (r + 1)) := by
  apply simple_root_centralizer r A
  · intro i
    have h := hA (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator
      (CartanMatrix.C (r + 1)).transpose (CartanMatrix.Generators.E i))
    simpa only [symplecticBaseChange_E] using h
  · intro i
    have h := hA (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator
      (CartanMatrix.C (r + 1)).transpose (CartanMatrix.Generators.F i))
    simpa only [symplecticBaseChange_F] using h

theorem unit_conjugation_fix_iff_commute {R : Type*} [Ring R] (u : Rˣ) (x : R) :
    (u : R) * x * (↑(u⁻¹) : R) = x ↔ (u : R) * x = x * (u : R) := by
  constructor
  · intro h
    have hh := congrArg (fun y : R => y * (u : R)) h
    simpa only [mul_assoc, Units.inv_mul, mul_one] using hh
  · intro h
    rw [h, mul_assoc, Units.mul_inv, mul_one]

theorem symplecticImage_conjugation_kernel_scalar (K : Type*) [CommRing K] (r : ℕ)
    (u : (Mat K (r + 1))ˣ)
    (hu : ∀ x : K ⊗[ℤ] integralLattice (CartanMatrix.C (r + 1)).transpose,
      (u : Mat K (r + 1)) * symplecticBaseChange K (r + 1) x * (↑(u⁻¹) : Mat K (r + 1)) =
        symplecticBaseChange K (r + 1) x) :
    ∃ c : K, (u : Mat K (r + 1)) = c • (1 : Mat K (r + 1)) := by
  apply symplecticImage_centralizer K r (u : Mat K (r + 1))
  intro x
  exact (unit_conjugation_fix_iff_commute u _).mp (hu x)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
