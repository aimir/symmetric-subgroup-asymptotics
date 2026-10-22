import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeylRotations
import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotationMonomial
import SymmetricSubgroupAsymptotics.CFSGMonomialProductCoordinates

/-! The actual relative Weyl word has a literal signed monomial chart.
The raw four-swap permutation and every row weight are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeylMonomial
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGMatrixPairRotation CFSGTwistedDPairedWeyl CFSGTwistedDPairedWeylRotations
open CFSGTypeAMonomialMatrices CFSGMonomialProductCoordinates

def firstSwap (s : ℕ) : Equiv.Perm (Index (s + 4)) :=
  Equiv.swap (Sum.inl (pen (s + 2))) (Sum.inl (last (s + 2)))
def secondSwap (s : ℕ) : Equiv.Perm (Index (s + 4)) :=
  Equiv.swap (Sum.inr (pen (s + 2))) (Sum.inr (last (s + 2)))
def thirdSwap (s : ℕ) : Equiv.Perm (Index (s + 4)) :=
  Equiv.swap (Sum.inl (pen (s + 2))) (Sum.inr (last (s + 2)))
def fourthSwap (s : ℕ) : Equiv.Perm (Index (s + 4)) :=
  Equiv.swap (Sum.inr (pen (s + 2))) (Sum.inl (last (s + 2)))

def pairedPermutation (s : ℕ) : Equiv.Perm (Index (s + 4)) :=
  (fourthSwap s * thirdSwap s) * (secondSwap s * firstSwap s)

def pairedWeights (K : Type) [Field K] (s : ℕ) (x : Index (s + 4)) : K :=
  ((if x = Sum.inl (pen (s + 2)) then -1 else 1) *
    (if firstSwap s x = Sum.inr (pen (s + 2)) then -1 else 1)) *
  ((if (secondSwap s * firstSwap s) x = Sum.inl (pen (s + 2)) then -1 else 1) *
    (if thirdSwap s ((secondSwap s * firstSwap s) x) = Sum.inr (pen (s + 2)) then -1 else 1))

theorem pairedWeights_ne_zero (K : Type) [Field K] (s : ℕ) (x : Index (s + 4)) :
    pairedWeights K s x ≠ 0 := by
  unfold pairedWeights
  split_ifs <;> simp

theorem pairedWeyl_monomial (s : ℕ) (q : CFSG.PrimePower) :
    ((pairedWeyl s q).val : Mat (q.Extension 2) (s + 4)) =
      monomial (pairedPermutation s) (pairedWeights (q.Extension 2) s) := by
  rw [pairedWeyl_rotations,
    rotation_monomial _ _ _ (fun h => pen_ne_last (s + 2) (Sum.inl.inj h)),
    rotation_monomial _ _ _ (fun h => pen_ne_last (s + 2) (Sum.inr.inj h)),
    rotation_monomial _ _ _ (by intro h; cases h),
    rotation_monomial _ _ _ (by intro h; cases h),
    monomial_mul, monomial_mul, monomial_mul]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeylMonomial
