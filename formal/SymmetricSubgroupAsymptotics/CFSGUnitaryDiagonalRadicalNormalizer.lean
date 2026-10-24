import SymmetricSubgroupAsymptotics.CFSGUnitaryRadicalNormalizerAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadicalSupport

/-! Literal diagonal fixed matrices normalize the actual two-axis
radical. The quotient formula is proved on actual matrix entries and
does not assert linearity for arbitrary radical-normalizer elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryUpperArrays

private def diagonalCoordinateUnit {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (d : I → Kˣ) : (Matrix I I K)ˣ where
  val := Matrix.diagonal (fun i => (d i : K))
  inv := Matrix.diagonal (fun i => ((d i)⁻¹ : K))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    change (if i = j then (d i : K) * ((d i)⁻¹ : K) else 0) =
      (if i = j then 1 else 0)
    by_cases hij : i = j <;> simp [hij]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    change (if i = j then ((d i)⁻¹ : K) * (d i : K) else 0) =
      (if i = j then 1 else 0)
    by_cases hij : i = j <;> simp [hij]

private theorem diagonalCoordinateUnit_conjugate_entry
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (d : I → Kˣ) (R : (Matrix I I K)ˣ) (i j : I) :
    ((diagonalCoordinateUnit d * R * (diagonalCoordinateUnit d)⁻¹ : (Matrix I I K)ˣ) :
      Matrix I I K) i j = (d i : K) * (R : Matrix I I K) i j * ((d j)⁻¹ : K) := by
  change (Matrix.diagonal (fun i => (d i : K)) * (R : Matrix I I K) *
    Matrix.diagonal (fun i => ((d i)⁻¹ : K))) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem diagonal_conjugate_mem_fixedRadical (q : CFSG.PrimePower) (t : ℕ)
    (a : naturalFixed (t + 2) q) (d : Fin (t + 3) → (q.Extension 2)ˣ)
    (ha : (a.val.val : Mat (q.Extension 2) (t + 2)) = Matrix.diagonal (fun i => (d i : q.Extension 2)))
    (g : naturalFixed (t + 2) q) (hg : g ∈ fixedRadical q t) :
    a * g * a⁻¹ ∈ fixedRadical q t := by
  have hu : a.val.val = diagonalCoordinateUnit d := Units.ext ha
  have he (i j : Fin (t + 3)) :
      ((a * g * a⁻¹).val.val : Mat (q.Extension 2) (t + 2)) i j =
        (d i : q.Extension 2) * (g.val.val : Mat (q.Extension 2) (t + 2)) i j *
          ((d j)⁻¹ : q.Extension 2) := by
    change ((a.val.val * g.val.val * a.val.val⁻¹ : (Mat (q.Extension 2) (t + 2))ˣ) :
      Mat (q.Extension 2) (t + 2)) i j = _
    rw [hu]
    exact diagonalCoordinateUnit_conjugate_entry d g.val.val i j
  obtain ⟨hd, hs⟩ := (mem_fixedRadical_iff_natural_support q t g).mp hg
  apply (mem_fixedRadical_iff_natural_support q t _).mpr
  constructor
  · intro i
    rw [he, hd]
    simp
  · intro i j hi hj
    rw [he, hs i j hi hj]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]

theorem diagonal_mem_unitaryRadicalNormalizer (q : CFSG.PrimePower) (t : ℕ)
    (a : naturalFixed (t + 2) q) (d : Fin (t + 3) → (q.Extension 2)ˣ)
    (ha : (a.val.val : Mat (q.Extension 2) (t + 2)) = Matrix.diagonal (fun i => (d i : q.Extension 2))) :
    a ∈ unitaryRadicalNormalizer q t := by
  have hu : a.val.val = diagonalCoordinateUnit d := Units.ext ha
  have hi : ((a⁻¹).val.val : Mat (q.Extension 2) (t + 2)) =
      Matrix.diagonal (fun i => ((d i)⁻¹ : q.Extension 2)) := by
    change ((a.val.val⁻¹ : (Mat (q.Extension 2) (t + 2))ˣ) : Mat (q.Extension 2) (t + 2)) = _
    rw [hu]
    rfl
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact diagonal_conjugate_mem_fixedRadical q t a d ha g
  · intro hg
    have hh := diagonal_conjugate_mem_fixedRadical q t a⁻¹ (fun i => (d i)⁻¹)
      (by simpa only [Units.val_inv_eq_inv_val] using hi)
      (a * g * a⁻¹) hg
    have he : a⁻¹ * (a * g * a⁻¹) * (a⁻¹)⁻¹ = g := by group
    rwa [he] at hh

theorem fixedRadicalParameterHom_natural_entry (q : CFSG.PrimePower) (t : ℕ)
    (g : fixedRadical q t) (i : Fin (t + 1)) :
    (fixedRadicalParameterHom q t g).toAdd i =
      (g.val.val.val : Mat (q.Extension 2) (t + 2))
        (splitEquiv t (.inr (.inl i))) (Fin.last (t + 2)) := by
  change (blockFixedMatrixHom q t g.val :
    Matrix (Index (Fin (t + 1))) (Index (Fin (t + 1))) (q.Extension 2))
      (.inr (.inl i)) (.inr (.inr ())) = _
  rw [blockFixedMatrixHom_apply]
  rfl

theorem unitaryDiagonalNormalizer_vector_action (q : CFSG.PrimePower) (t : ℕ)
    (a : naturalFixed (t + 2) q) (d : Fin (t + 3) → (q.Extension 2)ˣ)
    (ha : (a.val.val : Mat (q.Extension 2) (t + 2)) = Matrix.diagonal (fun i => (d i : q.Extension 2)))
    (v : Multiplicative (Fin (t + 1) → q.Extension 2)) (i : Fin (t + 1)) :
    (unitaryRadicalNormalizerVectorAutHom q t
      ⟨a, diagonal_mem_unitaryRadicalNormalizer q t a d ha⟩ v).toAdd i =
        (d (splitEquiv t (.inr (.inl i))) : q.Extension 2) * v.toAdd i *
          ((d (Fin.last (t + 2)))⁻¹ : q.Extension 2) := by
  obtain ⟨g, rfl⟩ := fixedRadicalParameterHom_surjective q t v
  rw [← unitaryRadicalNormalizer_parameter]
  rw [fixedRadicalParameterHom_natural_entry, fixedRadicalParameterHom_natural_entry]
  have hu : a.val.val = diagonalCoordinateUnit d := Units.ext ha
  change ((a.val.val * g.val.val.val * a.val.val⁻¹ : (Mat (q.Extension 2) (t + 2))ˣ) :
    Mat (q.Extension 2) (t + 2)) (splitEquiv t (.inr (.inl i))) (Fin.last (t + 2)) = _
  rw [hu]
  exact diagonalCoordinateUnit_conjugate_entry d g.val.val.val _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
