import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalNaturalImages
import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalMatrixCoordinates

/-! A genuine finite basis for the ORIGINAL rational Serre A quotient.
Negative interval vectors are normalized by integer unit signs. The
all-ring matrix coordinate table proves independence of this family;
spanning was proved independently using the original defining relations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
open CFSGTwistedANaturalMatrices

def basisSign (r : ℕ) : BasisIndex r → ℤ
  | .inl _ => 1
  | .inr (false, _) => 1
  | .inr (true, p) => (-1) ^ (p.val.2.val - p.val.1.val - 1)

theorem basisSign_square (R : Type*) [CommRing R] (r : ℕ) (i : BasisIndex r) :
    (basisSign r i : R) * (basisSign r i : R) = 1 := by
  rcases i with i | ⟨b, p⟩
  · simp only [basisSign, Int.cast_one, one_mul]
  · cases b
    · simp only [basisSign, Int.cast_one, one_mul]
    · simp only [basisSign, Int.cast_pow, Int.cast_neg, Int.cast_one]
      rw [← mul_pow]
      simp

def normalizedVectors (r : ℕ) (i : BasisIndex r) : Source r :=
  (basisSign r i : ℚ) • basisVectors r i

def normalizedSpan (r : ℕ) : Submodule ℚ (Source r) :=
  Submodule.span ℚ (Set.range (normalizedVectors r))

theorem normalizedSpan_eq_top (r : ℕ) : normalizedSpan r = ⊤ := by
  apply top_unique
  rw [← finiteSpan_eq_top r]
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  have h := (normalizedSpan r).smul_mem (basisSign r i : ℚ)
    (Submodule.subset_span (s := Set.range (normalizedVectors r)) ⟨i, rfl⟩)
  simpa only [normalizedVectors, smul_smul, basisSign_square, one_smul] using h

def normalizedCombination (r : ℕ) : (BasisIndex r → ℚ) →ₗ[ℚ] Source r :=
  Fintype.linearCombination ℚ (normalizedVectors r)

theorem normalizedCombination_surjective (r : ℕ) :
    Function.Surjective (normalizedCombination r) := by
  apply LinearMap.range_eq_top.mp
  exact (Fintype.range_linearCombination ℚ (normalizedVectors r)).trans (normalizedSpan_eq_top r)

theorem natural_rootInterval_positive (r : ℕ) (p : RootPair r) :
    rationalNatural r (rootInterval r false p) = Matrix.single p.val.1 p.val.2 1 := by
  have hp : p.val.1.val < p.val.2.val := p.property
  have htop := p.val.2.isLt
  have he : p.val.1.val + (p.val.2.val - p.val.1.val) = p.val.2.val := by omega
  have h := natural_interval_positive r p.val.1.val (p.val.2.val - p.val.1.val)
    (by omega) (by omega)
  simpa only [rootInterval, he] using h

theorem natural_rootInterval_negative (r : ℕ) (p : RootPair r) :
    rationalNatural r (rootInterval r true p) = Matrix.single p.val.2 p.val.1
      ((-1 : ℚ) ^ (p.val.2.val - p.val.1.val - 1)) := by
  have hp : p.val.1.val < p.val.2.val := p.property
  have htop := p.val.2.isLt
  have he : p.val.1.val + (p.val.2.val - p.val.1.val) = p.val.2.val := by omega
  have h := natural_interval_negative r p.val.1.val (p.val.2.val - p.val.1.val)
    (by omega) (by omega)
  simpa only [rootInterval, he] using h

theorem rationalNatural_normalizedVectors (r : ℕ) (i : BasisIndex r) :
    rationalNatural r (normalizedVectors r i) = CFSGTwistedAIntervalMatrixCoordinates.matrixVectors ℚ r i := by
  rw [normalizedVectors, map_smul]
  rcases i with i | ⟨b, p⟩
  · simpa only [basisSign, Int.cast_one, one_smul, basisVectors, cartan, CFSGTwistedAIntervalMatrixCoordinates.matrixVectors]
      using rationalNatural_H r i
  · cases b
    · simpa only [basisSign, Int.cast_one, one_smul, basisVectors, CFSGTwistedAIntervalMatrixCoordinates.matrixVectors] using
        natural_rootInterval_positive r p
    · rw [basisVectors, natural_rootInterval_negative, Matrix.smul_single]
      have hs : ((-1 : ℚ) ^ (p.val.2.val - p.val.1.val - 1)) *
          ((-1 : ℚ) ^ (p.val.2.val - p.val.1.val - 1)) = 1 := by
        simpa only [basisSign, Int.cast_pow, Int.cast_neg, Int.cast_one] using
          basisSign_square ℚ r (.inr (true, p))
      simp only [basisSign, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_eq_mul, hs]
      rfl

def rationalCoordinates (r : ℕ) : Source r →ₗ[ℚ] (BasisIndex r → ℚ) :=
  (CFSGTwistedAIntervalMatrixCoordinates.matrixCoordinates ℚ r).comp (rationalNatural r).toLinearMap

theorem rationalNatural_combination (r : ℕ) (a : BasisIndex r → ℚ) :
    rationalNatural r (normalizedCombination r a) = CFSGTwistedAIntervalMatrixCoordinates.matrixCombination ℚ r a := by
  change rationalNatural r (∑ i, a i • normalizedVectors r i) =
    ∑ i, a i • CFSGTwistedAIntervalMatrixCoordinates.matrixVectors ℚ r i
  simp only [map_sum, map_smul, rationalNatural_normalizedVectors]

theorem rationalCoordinates_combination (r : ℕ) (a : BasisIndex r → ℚ) :
    rationalCoordinates r (normalizedCombination r a) = a := by
  change CFSGTwistedAIntervalMatrixCoordinates.matrixCoordinates ℚ r (rationalNatural r (normalizedCombination r a)) = a
  rw [rationalNatural_combination, CFSGTwistedAIntervalMatrixCoordinates.coordinates_combination]

theorem combination_rationalCoordinates (r : ℕ) (x : Source r) :
    normalizedCombination r (rationalCoordinates r x) = x := by
  obtain ⟨a, rfl⟩ := normalizedCombination_surjective r x
  rw [rationalCoordinates_combination]

def rationalBasisEquiv (r : ℕ) : Source r ≃ₗ[ℚ] (BasisIndex r → ℚ) where
  __ := rationalCoordinates r
  invFun := normalizedCombination r
  left_inv := combination_rationalCoordinates r
  right_inv := rationalCoordinates_combination r

theorem rationalNatural_injective (r : ℕ) : Function.Injective (rationalNatural r) := by
  intro x y h
  apply (rationalBasisEquiv r).injective
  exact congrArg (CFSGTwistedAIntervalMatrixCoordinates.matrixCoordinates ℚ r) h

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
