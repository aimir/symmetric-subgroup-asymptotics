import SymmetricSubgroupAsymptotics.CFSGSymplecticIntegralOperators
import SymmetricSubgroupAsymptotics.CFSGSquareZeroConjugation
import SymmetricSubgroupAsymptotics.CFSGAlgebraConjugationAction
import Mathlib.Algebra.Group.Subgroup.Basic

/-! A literal group of natural symplectic root transvections in matrix
units, distinct from the original Serre model. No equivalence between
the two groups or identification with the full symplectic group is
asserted by this definition. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def rootTransvection (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) : (Mat K r)ˣ where
  val := 1 + t • rootMatrix K r neg i
  inv := 1 - t • rootMatrix K r neg i
  val_inv := CFSGSquareZeroConjugation.transvection_mul_inverse t _ (rootMatrix_sq_zero K r neg i)
  inv_val := CFSGSquareZeroConjugation.inverse_mul_transvection t _ (rootMatrix_sq_zero K r neg i)

@[simp] theorem rootTransvection_val (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) :
    (rootTransvection K r neg i t : Mat K r) = 1 + t • rootMatrix K r neg i := rfl

@[simp] theorem rootTransvection_inv_val (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) :
    (↑((rootTransvection K r neg i t)⁻¹) : Mat K r) = 1 - t • rootMatrix K r neg i := rfl

def elementaryRootGroup (K : Type*) [CommRing K] (r : ℕ) : Subgroup ((Mat K r)ˣ) :=
  Subgroup.closure {u | ∃ neg i t, u = rootTransvection K r neg i t}

theorem rootTransvection_mem (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) :
    rootTransvection K r neg i t ∈ elementaryRootGroup K r :=
  Subgroup.subset_closure ⟨neg, i, t, rfl⟩

theorem rootTransvection_conjugation (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) (X : Mat K r) :
    CFSGAlgebraConjugationAction.action K (Mat K r) (rootTransvection K r neg i t) X =
      (1 + t • rootMatrix K r neg i) * X * (1 - t • rootMatrix K r neg i) := rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
