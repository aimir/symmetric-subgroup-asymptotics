import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotent

/-! The first two original flag vectors under actual D-unipotent U.
The first is fixed and the second changes only by a scalar multiple
of the first; hence their exterior pair is fixed without any split
or model-identification premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
variable (K : Type) [Field K]

def firstVector (s : ℕ) : Index (s + 4) → K := Pi.single (Sum.inl 0) 1
def secondIndex (s : ℕ) : Fin (s + 4) := ⟨1, by omega⟩
def secondVector (s : ℕ) : Index (s + 4) → K := Pi.single (Sum.inl (secondIndex s)) 1

theorem zero_ne_second (s : ℕ) : (0 : Fin (s + 4)) ≠ secondIndex s := by
  intro h
  have hv := congrArg Fin.val h
  change 0 = 1 at hv
  omega

theorem unipotent_firstVector (s : ℕ) (g : unipotent K (s + 4)) :
    (g.val.val : Mat K (s + 4)) *ᵥ firstVector K s = firstVector K s := by
  rw [firstVector, Matrix.mulVec_single_one]
  funext x
  cases x with
  | inl i =>
    by_cases hi : i = 0
    · subst i
      simpa only [Matrix.col_apply, Pi.single_eq_same] using g.property.2 (Sum.inl 0)
    · have hlt : flagEquiv (s + 4) (Sum.inl (0 : Fin (s + 4))) <
          flagEquiv (s + 4) (Sum.inl i) := by
        change 0 < i.val
        have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      have hz := g.property.1 hlt
      simpa [Matrix.col_apply, Pi.single_apply, hi, Ne.symm hi] using hz
  | inr i => simpa [Matrix.col_apply, Pi.single_apply] using unipotent_lower_left_zero K (s + 4) g i 0

theorem unipotent_secondVector (s : ℕ) (g : unipotent K (s + 4)) :
    (g.val.val : Mat K (s + 4)) *ᵥ secondVector K s = secondVector K s +
      (g.val.val : Mat K (s + 4)) (Sum.inl 0) (Sum.inl (secondIndex s)) • firstVector K s := by
  rw [secondVector, Matrix.mulVec_single_one]
  funext x
  cases x with
  | inl i =>
    by_cases hi0 : i = 0
    · subst i
      simp [Matrix.col_apply, Pi.single_apply, firstVector, zero_ne_second, Ne.symm (zero_ne_second s)]
    · by_cases hi1 : i = secondIndex s
      · subst i
        simpa [Matrix.col_apply, Pi.single_apply, firstVector, secondVector,
          zero_ne_second, Ne.symm (zero_ne_second s)] using g.property.2 (Sum.inl (secondIndex s))
      · have hlt : flagEquiv (s + 4) (Sum.inl (secondIndex s)) < flagEquiv (s + 4) (Sum.inl i) := by
          change 1 < i.val
          have hne0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          have hne1 : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
          omega
        have hz := g.property.1 hlt
        simpa [Matrix.col_apply, Pi.single_apply, firstVector, secondVector,
          hi0, Ne.symm hi0, hi1, Ne.symm hi1] using hz
  | inr i =>
    simpa [Matrix.col_apply, Pi.single_apply, firstVector, secondVector] using
      unipotent_lower_left_zero K (s + 4) g i (secondIndex s)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexFlagVectors
