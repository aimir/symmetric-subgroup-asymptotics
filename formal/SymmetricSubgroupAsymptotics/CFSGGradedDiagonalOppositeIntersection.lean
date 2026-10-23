import SymmetricSubgroupAsymptotics.CFSGGradedMatrixOpposite
import Mathlib.Data.Matrix.Mul

/-! A strictly graded unipotent times a diagonal matrix cannot be
oppositely unipotent unless both factors are one. This uses only actual
matrix entries and works in every characteristic and with weight blocks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedDiagonalOppositeIntersection
open CFSGGradedMatrixSubgroups
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem strict_diagonal_eq_one (weight : I → ℤ) (u : (Matrix I I K)ˣ)
    (hu : u ∈ strictUnits weight)
    (hd : ∃ a : I → K, (u : Matrix I I K) = Matrix.diagonal a) : u = 1 := by
  obtain ⟨a, ha⟩ := hd
  apply Units.ext
  ext i j
  change (u : Matrix I I K) i j = (1 : Matrix I I K) i j
  by_cases hij : i = j
  · subst j; exact hu i i le_rfl
  · rw [ha, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem factors_eq_one (weight : I → ℤ) (u d : (Matrix I I K)ˣ)
    (hu : u ∈ strictUnits weight)
    (hd : ∃ a : I → K, (d : Matrix I I K) = Matrix.diagonal a)
    (hv : u * d ∈ strictUnits (fun i => -weight i)) : d = 1 ∧ u = 1 := by
  obtain ⟨a, ha⟩ := hd
  have hai (i : I) : a i = 1 := by
    have hh : ((u * d : (Matrix I I K)ˣ) : Matrix I I K) i i = 1 := by
      simpa only [Matrix.one_apply_eq] using hv i i le_rfl
    rw [Units.val_mul, ha, Matrix.mul_diagonal] at hh
    have hui : (u : Matrix I I K) i i = 1 := by
      simpa only [Matrix.one_apply_eq] using hu i i le_rfl
    simpa only [hui, one_mul] using hh
  have hd1 : d = 1 := by
    apply Units.ext
    change (d : Matrix I I K) = (1 : Matrix I I K)
    rw [ha]
    ext i j
    by_cases hij : i = j
    · subst j; simp only [Matrix.diagonal_apply_eq, hai, Matrix.one_apply_eq]
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hi : u ∈ strictUnits weight ⊓ strictUnits (fun i => -weight i) :=
    ⟨hu, by simpa only [hd1, mul_one] using hv⟩
  rw [strict_inf_opposite, Subgroup.mem_bot] at hi
  exact ⟨hd1, hi⟩

theorem envelope_disjoint_opposite (weight : I → ℤ)
    (B U D V : Subgroup (Matrix I I K)ˣ)
    (hU : U ≤ strictUnits weight) (hV : V ≤ strictUnits (fun i => -weight i))
    (hD : ∀ d ∈ D, ∃ a : I → K, (d : Matrix I I K) = Matrix.diagonal a)
    (hfactor : ∀ b ∈ B, ∃ u ∈ U, ∃ d ∈ D, b = u * d) : Disjoint B V := by
  apply Subgroup.disjoint_def.mpr
  intro b hb hv
  obtain ⟨u, hu, d, hd, he⟩ := hfactor b hb
  have hh := factors_eq_one weight u d (hU hu) (hD d hd) (he ▸ hV hv)
  rw [he, hh.1, hh.2, mul_one]

end SymmetricSubgroupAsymptotics.CFSGGradedDiagonalOppositeIntersection
