import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPairedWeyl
import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotationMonomial
import SymmetricSubgroupAsymptotics.CFSGMonomialProductCoordinates

/-! All-rank signed monomial chart of the literal paired Weyl word.
The last two pairs flip, with coefficient minus one; the original
rank-two and rank-three coordinate carriers are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankWeylCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGMatrixPairRotation CFSGTwistedDAllRankPairedWeyl
open CFSGTypeAMonomialMatrices CFSGMonomialProductCoordinates

def firstSwap (n : ℕ) : Equiv.Perm (Index (n + 2)) :=
  Equiv.swap (Sum.inl (pen n)) (Sum.inl (last n))
def secondSwap (n : ℕ) : Equiv.Perm (Index (n + 2)) :=
  Equiv.swap (Sum.inr (pen n)) (Sum.inr (last n))
def thirdSwap (n : ℕ) : Equiv.Perm (Index (n + 2)) :=
  Equiv.swap (Sum.inl (pen n)) (Sum.inr (last n))
def fourthSwap (n : ℕ) : Equiv.Perm (Index (n + 2)) :=
  Equiv.swap (Sum.inr (pen n)) (Sum.inl (last n))

def pairedPermutation (n : ℕ) : Equiv.Perm (Index (n + 2)) :=
  (fourthSwap n * thirdSwap n) * (secondSwap n * firstSwap n)

def pairedWeights (K : Type) [Field K] (n : ℕ) (x : Index (n + 2)) : K :=
  ((if x = Sum.inl (pen n) then -1 else 1) *
    (if firstSwap n x = Sum.inr (pen n) then -1 else 1)) *
  ((if (secondSwap n * firstSwap n) x = Sum.inl (pen n) then -1 else 1) *
    (if thirdSwap n ((secondSwap n * firstSwap n) x) = Sum.inr (pen n) then -1 else 1))

theorem pairedWeights_ne_zero (K : Type) [Field K] (n : ℕ) (x : Index (n + 2)) :
    pairedWeights K n x ≠ 0 := by
  unfold pairedWeights
  split_ifs <;> simp

theorem weyl_monomial (n : ℕ) (q : CFSG.PrimePower) :
    ((weyl n q).val : Mat (q.Extension 2) (n + 2)) =
      monomial (pairedPermutation n) (pairedWeights (q.Extension 2) n) := by
  rw [weyl_rotations,
    rotation_monomial _ _ _ (fun h => pen_ne_last n (Sum.inl.inj h)),
    rotation_monomial _ _ _ (fun h => pen_ne_last n (Sum.inr.inj h)),
    rotation_monomial _ _ _ (by intro h; cases h),
    rotation_monomial _ _ _ (by intro h; cases h),
    monomial_mul, monomial_mul, monomial_mul]
  rfl

theorem permutation_positive (n : ℕ) (i : Fin (n + 2)) :
    pairedPermutation n (Sum.inl i) =
      if i = pen n then Sum.inr (pen n)
      else if i = last n then Sum.inr (last n) else Sum.inl i := by
  by_cases hp : i = pen n
  · subst i
    simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last n)]
  · by_cases hl : i = last n
    · subst i
      simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last n)]
    · simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, hp, hl, Ne.symm hp, Ne.symm hl]

theorem permutation_negative (n : ℕ) (i : Fin (n + 2)) :
    pairedPermutation n (Sum.inr i) =
      if i = pen n then Sum.inl (pen n)
      else if i = last n then Sum.inl (last n) else Sum.inr i := by
  by_cases hp : i = pen n
  · subst i
    simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last n)]
  · by_cases hl : i = last n
    · subst i
      simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last n)]
    · simp [pairedPermutation, firstSwap, secondSwap, thirdSwap, fourthSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, hp, hl, Ne.symm hp, Ne.symm hl]

theorem weights_positive (K : Type) [Field K] (n : ℕ) (i : Fin (n + 2)) :
    pairedWeights K n (Sum.inl i) =
      if i = pen n then -1 else if i = last n then -1 else 1 := by
  by_cases hp : i = pen n
  · subst i
    simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last n)]
  · by_cases hl : i = last n
    · subst i
      simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last n)]
    · simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, hp, hl, Ne.symm hp, Ne.symm hl]

theorem weights_negative (K : Type) [Field K] (n : ℕ) (i : Fin (n + 2)) :
    pairedWeights K n (Sum.inr i) =
      if i = pen n then -1 else if i = last n then -1 else 1 := by
  by_cases hp : i = pen n
  · subst i
    simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last n)]
  · by_cases hl : i = last n
    · subst i
      simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, pen_ne_last, Ne.symm (pen_ne_last n)]
    · simp [pairedWeights, firstSwap, secondSwap, thirdSwap,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def, hp, hl, Ne.symm hp, Ne.symm hl]

theorem permutation_involutive (n : ℕ) : Function.Involutive (pairedPermutation n) := by
  intro x
  cases x with
  | inl i =>
    by_cases hp : i = pen n
    · subst i
      simp [permutation_positive, permutation_negative]
    · by_cases hl : i = last n
      · subst i
        simp [permutation_positive, permutation_negative, pen_ne_last, Ne.symm (pen_ne_last n)]
      · simp [permutation_positive, hp, hl]
  | inr i =>
    by_cases hp : i = pen n
    · subst i
      simp [permutation_positive, permutation_negative]
    · by_cases hl : i = last n
      · subst i
        simp [permutation_positive, permutation_negative, pen_ne_last, Ne.symm (pen_ne_last n)]
      · simp [permutation_negative, hp, hl]

theorem permutation_symm_eq (n : ℕ) : (pairedPermutation n).symm = pairedPermutation n := by
  apply Equiv.ext
  intro x
  exact (pairedPermutation n).symm_apply_eq.mpr ((permutation_involutive n x).symm)

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankWeylCoordinates
