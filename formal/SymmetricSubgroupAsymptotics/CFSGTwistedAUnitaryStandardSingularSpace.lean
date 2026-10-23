import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySubspaceCompression
import Mathlib.Tactic.FinCases

/-! A literal standard totally isotropic subspace: vectors are supported
on coordinates i with 2*i+1 <= r. Its isotropy and compatibility with
the original middle embedding are proved from the actual signed
reversal entries. No Witt-index or classical-group order formula enters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists
open CFSGHermitianHyperbolicCompression

def unitaryStandardSingularSpace (q : CFSG.PrimePower) (r : ℕ) :
    Submodule (q.Extension 2) (Fin (r + 1) → q.Extension 2) where
  carrier := {x | ∀ i, r < 2 * i.val + 1 → x i = 0}
  zero_mem' := by intro i hi; rfl
  add_mem' hx hy := by intro i hi; simp only [Pi.add_apply, hx i hi, hy i hi, add_zero]
  smul_mem' a x hx := by intro i hi; simp only [Pi.smul_apply, hx i hi, smul_zero]

theorem unitaryStandardSingularSpace_pair_zero (q : CFSG.PrimePower) (r : ℕ) :
    ∀ x ∈ unitaryStandardSingularSpace q r,
      ∀ y ∈ unitaryStandardSingularSpace q r, unitaryNaturalPair q r x y = 0 := by
  intro x hx y hy
  have hrow (i : Fin (r + 1)) :
      ((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ y) i =
        signWeight (q.Extension 2) r i * y i.rev := by
    simp [Matrix.mulVec, dotProduct, signedReversalUnit_apply, ite_mul, eq_comm]
  change (∑ i : Fin (r + 1), definingFieldAutomorphism q 2 (x i) *
    (((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ y) i)) = 0
  apply Finset.sum_eq_zero
  intro i _
  rw [hrow]
  by_cases hi : r < 2 * i.val + 1
  · rw [hx i hi, map_zero, zero_mul]
  · have hrev : r < 2 * i.rev.val + 1 := by
      have hv : i.rev.val = r - i.val := by rw [Fin.val_rev]; omega
      have hib := i.isLt
      omega
    rw [hy i.rev hrev, mul_zero, mul_zero]

theorem unitaryStandardSingularSpace_head (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) :
    Pi.single (0 : Fin (r + 1)) 1 ∈ unitaryStandardSingularSpace q r := by
  intro i hi
  have hn : i ≠ 0 := by
    intro h
    subst i
    simp only [Fin.val_zero, mul_zero, zero_add] at hi
    omega
  change (Pi.single (0 : Fin (r + 1)) (1 : q.Extension 2) : Fin (r + 1) → q.Extension 2) i = 0
  simp only [Pi.single_apply, if_neg hn]

theorem unitaryStandardSingularSpace_rank_one (q : CFSG.PrimePower)
    (x : Fin 2 → q.Extension 2) : x ∈ unitaryStandardSingularSpace q 1 ↔ x 1 = 0 := by
  constructor
  · intro hx
    exact hx 1 (by decide)
  · intro hx i hi
    fin_cases i
    · norm_num at hi
    · exact hx

theorem unitaryStandardSingularSpace_middle (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) (hv : v ∈ unitaryStandardSingularSpace q s) :
    unitaryMiddleVector q s v ∈ unitaryStandardSingularSpace q (s + 2) := by
  intro i hi
  obtain ⟨p, rfl⟩ := (splitEquiv s).surjective i
  have he : unitaryMiddleVector q s v (splitEquiv s p) = middleVector v p := by
    change middleVector v ((splitEquiv s).symm (splitEquiv s p)) = _
    rw [Equiv.symm_apply_apply]
  rw [he]
  rcases p with u | (j | u)
  · rfl
  · change v j = 0
    apply hv j
    change s + 2 < 2 * (j.val + 1) + 1 at hi
    omega
  · rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
