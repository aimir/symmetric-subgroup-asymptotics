import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarHermitianEquiv
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarPoints
import SymmetricSubgroupAsymptotics.CFSGTwoPlaneShearAction

/-! A normalized rank-one Hermitian coefficient is the ACTUAL natural
rank-one unitary transvection on its displayed singular vector. The
formula is proved entrywise in the literal four-coordinate shear and
retains the original signed pairing in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists

def starRankOneParameters (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (htc : t ∈ centralParameters q (s + 1))
    (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a)
    (v : Fin 2 → q.Extension 2) : StarParameters q s :=
  starHermitianInverse q s t htc
    (CFSGHermitianTwoByTwoRankOne.rankOneParameter (definingFieldAutomorphism q 2)
      (fun z => extension_two_pow_twice q z) a ha v)

theorem starRankOne_coefficient (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (htc : t ∈ centralParameters q (s + 1))
    (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a)
    (v : Fin 2 → q.Extension 2) :
    starCoefficient q s (starRankOneParameters q s t htc a ha v) =
      !![(t * a) * v 0 * definingFieldAutomorphism q 2 (v 0),
          -((t * a) * v 0 * definingFieldAutomorphism q 2 (v 1));
        (t * a) * v 1 * definingFieldAutomorphism q 2 (v 0),
          -((t * a) * v 1 * definingFieldAutomorphism q 2 (v 1))] := by
  have hσ (z : q.Extension 2) : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 z) = z :=
    extension_two_pow_twice q z
  ext i j
  fin_cases i <;> fin_cases j
  · change t * (a * v 0 * definingFieldAutomorphism q 2 (v 0)) =
      (t * a) * v 0 * definingFieldAutomorphism q 2 (v 0)
    ring
  · change parity q (s + 1) * definingFieldAutomorphism q 2
      (t * (a * v 1 * definingFieldAutomorphism q 2 (v 0))) =
      -((t * a) * v 0 * definingFieldAutomorphism q 2 (v 1))
    simp only [map_mul, centralParameter_sigma q (s + 1) t htc, ha, hσ]
    rcases neg_one_pow_eq_or (q.Extension 2) (s + 1) with he | he
    · have he' : parity q (s + 1) = 1 := he
      rw [he']
      ring
    · have he' : parity q (s + 1) = -1 := he
      rw [he']
      ring
  · change t * (a * v 1 * definingFieldAutomorphism q 2 (v 0)) =
      (t * a) * v 1 * definingFieldAutomorphism q 2 (v 0)
    ring
  · change -(t * (a * v 1 * definingFieldAutomorphism q 2 (v 1))) =
      -((t * a) * v 1 * definingFieldAutomorphism q 2 (v 1))
    ring

theorem starRankOne_action (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (htc : t ∈ centralParameters q (s + 1))
    (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a)
    (v : Fin 2 → q.Extension 2) (x : Fin (s + 4) → q.Extension 2) :
    (((starFixed q s (starRankOneParameters q s t htc a ha v)).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ x) =
      x + ((t * a) * unitaryNaturalPair q (s + 3) (starVector q s v) x) • starVector q s v := by
  rw [starFixed_matrix]
  change (1 + CFSGTwoPlaneShearArrays.array (starPositive s) (starNegative s)
    (starCoefficient q s (starRankOneParameters q s t htc a ha v))) *ᵥ x = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, CFSGTwoPlaneShearArrays.array_mulVec,
    starRankOne_coefficient, starVector_pair]
  ext k
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.add_apply, Pi.smul_apply, starVector, Pi.single_apply]
  by_cases hk0 : k = starPositive s 0 <;> by_cases hk1 : k = starPositive s 1
  all_goals simp only [hk0, hk1, if_true, if_false]
  all_goals (try split_ifs) <;> ring

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
