import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalRationalBasis
import Mathlib.Algebra.Module.NatInt

/-! An actual integral basis for the ORIGINAL type-A divided-power-stable
lattice, every rank. Degree-one divided powers put interval vectors in
that same lattice. Integer natural coordinates then give a two-sided
integral inverse, rather than reducing rational injectivity modulo p. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalMatrixCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAIntervalSource

theorem coordinates_map {R S : Type*} [CommRing R] [CommRing S]
    (r : ℕ) (f : R →+* S) (M : Mat R r) :
    matrixCoordinates S r (f.mapMatrix M) = fun i => f (matrixCoordinates R r M i) := by
  funext i
  rcases i with i | ⟨b, p⟩
  · change (∑ j : Fin (r + 1), if j.val ≤ i.val then f (M j j) else 0) =
      f (∑ j : Fin (r + 1), if j.val ≤ i.val then M j j else 0)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  · cases b <;> rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalMatrixCoordinates

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGTwistedANaturalMatrices
open CFSGTwistedAIntervalBrackets CFSGSerreSquareZeroMatrix
open CFSGTwistedAIntervalMatrixCoordinates

theorem simple_mem_lattice (r : ℕ) (neg : Bool) (k : ℕ) :
    simple r neg k ∈ integralLattice (CartanMatrix.A r) := by
  by_cases hk : k < r
  · rw [simple, dif_pos hk]
    cases neg
    · exact generator_mem_integralLattice (CartanMatrix.A r) (.E ⟨k, hk⟩)
    · exact generator_mem_integralLattice (CartanMatrix.A r) (.F ⟨k, hk⟩)
  · rw [simple, dif_neg hk]
    exact (integralLattice (CartanMatrix.A r)).zero_mem

theorem interval_mem_lattice (r : ℕ) (neg : Bool) (start n : ℕ) :
    interval r neg start n ∈ integralLattice (CartanMatrix.A r) := by
  induction n using Nat.twoStepInduction generalizing start with
  | zero =>
    rw [interval, chainBracket_zero]
    exact (integralLattice (CartanMatrix.A r)).zero_mem
  | one => rw [interval_one]; exact simple_mem_lattice r neg start
  | more n _ ih =>
    rw [interval_step]
    by_cases hk : start < r
    · have h := dividedPower_mem (CartanMatrix.A r) neg ⟨start, hk⟩ 1
        (interval r neg (start + 1) (n + 1)) (ih (start + 1))
      simpa only [dividedPower, Nat.factorial_one, Nat.cast_one, inv_one,
        one_smul, pow_one, LinearMap.restrictScalars_apply, LieAlgebra.ad_apply,
        simple, dif_pos hk] using h
    · rw [simple, dif_neg hk, zero_lie]
      exact (integralLattice (CartanMatrix.A r)).zero_mem

theorem basisVectors_mem_lattice (r : ℕ) (i : BasisIndex r) :
    basisVectors r i ∈ integralLattice (CartanMatrix.A r) := by
  rcases i with i | ⟨b, p⟩
  · exact generator_mem_integralLattice (CartanMatrix.A r) (.H i)
  · exact interval_mem_lattice r b p.val.1.val (p.val.2.val - p.val.1.val)

theorem normalizedVectors_mem_lattice (r : ℕ) (i : BasisIndex r) :
    normalizedVectors r i ∈ integralLattice (CartanMatrix.A r) := by
  have h := (integralLattice (CartanMatrix.A r)).smul_mem (basisSign r i)
    (basisVectors_mem_lattice r i)
  simpa only [normalizedVectors, Int.cast_smul_eq_zsmul] using h

def integralVectors (r : ℕ) (i : BasisIndex r) : integralLattice (CartanMatrix.A r) :=
  ⟨normalizedVectors r i, normalizedVectors_mem_lattice r i⟩

theorem integralRepresentation_vectors (r : ℕ) (i : BasisIndex r) :
    integralRepresentation (realizationData r) (integralVectors r i) = matrixVectors ℤ r i := by
  apply integerCast_injective (Fin (r + 1))
  rw [integralRepresentation_cast]
  change rationalNatural r (normalizedVectors r i) =
    (Int.castRingHom ℚ).mapMatrix (matrixVectors ℤ r i)
  rw [rationalNatural_normalizedVectors, map_matrixVectors]

def integralCoordinates (r : ℕ) :
    integralLattice (CartanMatrix.A r) →ₗ[ℤ] (BasisIndex r → ℤ) :=
  (matrixCoordinates ℤ r).comp (integralRepresentation (realizationData r))

def integralCombination (r : ℕ) :
    (BasisIndex r → ℤ) →ₗ[ℤ] integralLattice (CartanMatrix.A r) :=
  Fintype.linearCombination ℤ (integralVectors r)

theorem integralCoordinates_vectors (r : ℕ) (i : BasisIndex r) :
    integralCoordinates r (integralVectors r i) = Pi.single i 1 := by
  change matrixCoordinates ℤ r (integralRepresentation (realizationData r) (integralVectors r i)) = _
  rw [integralRepresentation_vectors, coordinates_vector]

theorem integralCoordinates_combination (r : ℕ) (a : BasisIndex r → ℤ) :
    integralCoordinates r (integralCombination r a) = a := by
  change integralCoordinates r (∑ i, a i • integralVectors r i) = a
  rw [map_sum]
  simp only [map_smul, integralCoordinates_vectors]
  funext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]

theorem integralCombination_val (r : ℕ) (a : BasisIndex r → ℤ) :
    (integralCombination r a).val = normalizedCombination r (fun i => (a i : ℚ)) := by
  change (integralLattice (CartanMatrix.A r)).subtype (∑ i, a i • integralVectors r i) =
    ∑ i, (a i : ℚ) • normalizedVectors r i
  simp only [map_sum, map_smul, integralVectors, Submodule.subtype_apply,
    Int.cast_smul_eq_zsmul]

theorem integralCoordinates_cast (r : ℕ) (x : integralLattice (CartanMatrix.A r)) :
    (fun i => (integralCoordinates r x i : ℚ)) = rationalCoordinates r x.val := by
  have h := coordinates_map r (Int.castRingHom ℚ)
    (integralRepresentation (realizationData r) x)
  change matrixCoordinates ℚ r (integerCast (Fin (r + 1))
    (integralRepresentation (realizationData r) x)) = _ at h
  rw [integralRepresentation_cast] at h
  exact h.symm

theorem integralCombination_coordinates (r : ℕ) (x : integralLattice (CartanMatrix.A r)) :
    integralCombination r (integralCoordinates r x) = x := by
  apply Subtype.ext
  rw [integralCombination_val, integralCoordinates_cast, combination_rationalCoordinates]

def integralBasisEquiv (r : ℕ) :
    integralLattice (CartanMatrix.A r) ≃ₗ[ℤ] (BasisIndex r → ℤ) where
  __ := integralCoordinates r
  invFun := integralCombination r
  left_inv := integralCombination_coordinates r
  right_inv := integralCoordinates_combination r

theorem integralCombination_surjective (r : ℕ) : Function.Surjective (integralCombination r) :=
  fun x => ⟨integralCoordinates r x, integralCombination_coordinates r x⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
