import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySubspaceCompression
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOuterWeyl

/-! The exact signed norm of (a,0,...,0,1), and the actual central
root carrying two such vectors with the same norm to one another. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryUpperArrays CFSGTwistedAUnitaryParameters
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists
open CFSGHermitianHyperbolicCompression

def unitaryTwoAxisVector (q : CFSG.PrimePower) (s : ℕ) (a : q.Extension 2) :
    Fin (s + 3) → q.Extension 2 :=
  Pi.single 0 a + Pi.single (Fin.last (s + 2)) 1

theorem unitaryTwoAxisVector_split (q : CFSG.PrimePower) (s : ℕ) (a : q.Extension 2) :
    unitarySplitLinearEquiv q s (unitaryTwoAxisVector q s a) =
      Pi.single (.inl ()) a + Pi.single (.inr (.inr ())) 1 := by
  have hfirst : splitEquiv s (.inl ()) = 0 := rfl
  have hlast : splitEquiv s (.inr (.inr ())) = Fin.last (s + 2) := rfl
  funext p
  change unitaryTwoAxisVector q s a (splitEquiv s p) = _
  simp only [unitaryTwoAxisVector, Pi.add_apply, Pi.single_apply, ← hfirst, ← hlast,
    (splitEquiv s).injective.eq_iff]

theorem unitaryTwoAxisVector_norm (q : CFSG.PrimePower) (s : ℕ) (a : q.Extension 2) :
    unitaryNaturalPair q (s + 2) (unitaryTwoAxisVector q s a) (unitaryTwoAxisVector q s a) =
      definingFieldAutomorphism q 2 a + parity q s * a := by
  rw [unitaryNaturalPair_split]
  simp only [unitaryTwoAxisVector_split, block_pair]
  have hm : middleProjection
      (Pi.single (.inl ()) a + Pi.single (.inr (.inr ())) (1 : q.Extension 2)) =
        (0 : Fin (s + 1) → q.Extension 2) := by
    funext i
    simp [middleProjection, Sum.inr.injEq]
  rw [hm]
  simp [hermitianPair]

theorem exists_central_two_axis_map (q : CFSG.PrimePower) (s : ℕ) (a b : q.Extension 2)
    (hab : definingFieldAutomorphism q 2 a + parity q s * a =
      definingFieldAutomorphism q 2 b + parity q s * b) :
    ∃ g : naturalFixed (s + 2) q,
      (g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ unitaryTwoAxisVector q s a =
        unitaryTwoAxisVector q s b := by
  have hb : Condition q s 0 (b - a) := by
    change definingFieldAutomorphism q 2 (b - a) + parity q s * (b - a) = _
    simp only [hermitianNorm, Matrix.mulVec_zero, dotProduct_zero, neg_zero]
    rw [map_sub]
    linear_combination -hab
  have hne : (0 : Fin (s + 3)) ≠ Fin.last (s + 2) := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = s + 2 at hv
    omega
  refine ⟨centralFixed q s (b - a) hb, ?_⟩
  have hmat : ((centralFixed q s (b - a) hb).val.val : Mat (q.Extension 2) (s + 2)) =
      1 + Matrix.single (0 : Fin (s + 3)) (Fin.last (s + 2)) (b - a) :=
    radicalCentral_matrix q s (b - a) hb
  rw [hmat, Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_single]
  have hl : unitaryTwoAxisVector q s a (Fin.last (s + 2)) = 1 := by
    simp [unitaryTwoAxisVector, Ne.symm hne]
  rw [hl, mul_one]
  ext i
  by_cases hi : i = 0 <;> simp [unitaryTwoAxisVector, Pi.single_apply, hi, hne] <;> ring

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
