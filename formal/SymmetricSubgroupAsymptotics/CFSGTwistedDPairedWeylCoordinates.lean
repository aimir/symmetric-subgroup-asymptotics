import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeylMonomial

/-! Exact coordinate and coefficient action of the actual relative
terminal Weyl word. Its permutation flips the last two paired positions;
all four moved coordinates have coefficient minus one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeylCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDPairedWeylMonomial

theorem permutation_positive (s : ℕ) (i : Fin (s + 4)) :
    pairedPermutation s (Sum.inl i) =
      if i = pen (s + 2) then Sum.inr (pen (s + 2))
      else if i = last (s + 2) then Sum.inr (last (s + 2)) else Sum.inl i := by
  by_cases hp : i = pen (s + 2)
  · subst i
    simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last (s + 2))]
  · by_cases hl : i = last (s + 2)
    · subst i
      simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last (s + 2))]
    · simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, hp, hl, Ne.symm hp, Ne.symm hl]

theorem permutation_negative (s : ℕ) (i : Fin (s + 4)) :
    pairedPermutation s (Sum.inr i) =
      if i = pen (s + 2) then Sum.inl (pen (s + 2))
      else if i = last (s + 2) then Sum.inl (last (s + 2)) else Sum.inr i := by
  by_cases hp : i = pen (s + 2)
  · subst i
    simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last (s + 2))]
  · by_cases hl : i = last (s + 2)
    · subst i
      simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last (s + 2))]
    · simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, hp, hl, Ne.symm hp, Ne.symm hl]

theorem weights_positive (K : Type) [Field K] (s : ℕ) (i : Fin (s + 4)) :
    pairedWeights K s (Sum.inl i) =
      if i = pen (s + 2) then -1 else if i = last (s + 2) then -1 else 1 := by
  by_cases hp : i = pen (s + 2)
  · subst i
    simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last (s + 2))]
  · by_cases hl : i = last (s + 2)
    · subst i
      simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last (s + 2))]
    · simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, hp, hl, Ne.symm hp, Ne.symm hl]

theorem weights_negative (K : Type) [Field K] (s : ℕ) (i : Fin (s + 4)) :
    pairedWeights K s (Sum.inr i) =
      if i = pen (s + 2) then -1 else if i = last (s + 2) then -1 else 1 := by
  by_cases hp : i = pen (s + 2)
  · subst i
    simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last (s + 2))]
  · by_cases hl : i = last (s + 2)
    · subst i
      simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last (s + 2))]
    · simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, hp, hl, Ne.symm hp, Ne.symm hl]

theorem permutation_involutive (s : ℕ) : Function.Involutive (pairedPermutation s) := by
  intro x
  cases x with
  | inl i =>
    by_cases hp : i = pen (s + 2)
    · subst i
      simp [permutation_positive, permutation_negative]
    · by_cases hl : i = last (s + 2)
      · subst i
        simp [permutation_positive, permutation_negative, pen_ne_last, Ne.symm (pen_ne_last (s + 2))]
      · simp [permutation_positive, hp, hl]
  | inr i =>
    by_cases hp : i = pen (s + 2)
    · subst i
      simp [permutation_positive, permutation_negative]
    · by_cases hl : i = last (s + 2)
      · subst i
        simp [permutation_positive, permutation_negative, pen_ne_last, Ne.symm (pen_ne_last (s + 2))]
      · simp [permutation_negative, hp, hl]

theorem permutation_symm_eq (s : ℕ) : (pairedPermutation s).symm = pairedPermutation s := by
  apply Equiv.ext
  intro x
  exact (pairedPermutation s).symm_apply_eq.mpr ((permutation_involutive s x).symm)

end SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeylCoordinates
