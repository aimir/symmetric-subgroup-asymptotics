import SymmetricSubgroupAsymptotics.CFSGGTwoHigherPositiveCommutation
import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveActionCoordinates
import Mathlib.Tactic.LinearCombination

/-! The two noncommuting simple/higher collecting rules and the six
commuting simple/higher pairs, with their literal six-root signs.
Characteristic three is used by the exact scalar equation 3=0, never
by dividing a structure constant. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSimpleHigherCollecting
open CFSGGTwoSerreMatrices CFSGGTwoPositiveDirections CFSGGTwoPositiveRootMatrices
open CFSGGTwoPositiveWordActions CFSGGTwoPositiveActionCoordinates

def commutingPair : Fin 6 → Fin 6 × Fin 6 :=
  ![(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)]

private theorem prime_linear (i : Fin 6) :
    Commute (positiveLinear (ZMod 3) (commutingPair i).1)
      (positiveLinear (ZMod 3) (commutingPair i).2) := by
  change _ * _ = _ * _
  fin_cases i <;> decide +kernel

private theorem prime_mixed (i : Fin 6) :
    Commute (positiveLinear (ZMod 3) (commutingPair i).1)
      (positiveQuadratic (ZMod 3) (commutingPair i).2) := by
  change _ * _ = _ * _
  fin_cases i <;> decide +kernel

private theorem prime_quadratic (i : Fin 6) :
    Commute (positiveQuadratic (ZMod 3) (commutingPair i).1)
      (positiveQuadratic (ZMod 3) (commutingPair i).2) := by
  change _ * _ = _ * _
  fin_cases i <;> decide +kernel

private theorem prime_reverse_mixed (i : Fin 6) :
    Commute (positiveQuadratic (ZMod 3) (commutingPair i).1)
      (positiveLinear (ZMod 3) (commutingPair i).2) := by
  change _ * _ = _ * _
  fin_cases i <;> decide +kernel

private theorem map_commute {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (X Y : Mat R) (h : Commute X Y) :
    Commute (f.mapMatrix X) (f.mapMatrix Y) := by
  change f.mapMatrix X*f.mapMatrix Y=f.mapMatrix Y*f.mapMatrix X
  rw [←map_mul,←map_mul,h.eq]

private theorem polynomial_commute {S B : Type*} [CommRing S] [Ring B] [Algebra S B]
    (E D F Q : B) (hEF : Commute E F) (hEQ : Commute E Q)
    (hDF : Commute D F) (hDQ : Commute D Q) (a b : S) :
    Commute (1+a • E+a^2 • D) (1+b • F+b^2 • Q) := by
  change _ * _ = _ * _
  simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,
    smul_smul,smul_add,hEF.eq,hEQ.eq,hDF.eq,hDQ.eq,
    mul_comm a b,mul_comm a (b^2),mul_comm (a^2) b,mul_comm (a^2) (b^2)]
  abel

variable (R : Type*) [CommRing R] [CharP R 3]

theorem polynomial_pair_commute (i : Fin 6) (a b : R) :
    Commute (polynomialRoot R (commutingPair i).1 a)
      (polynomialRoot R (commutingPair i).2 b) := by
  let f : ZMod 3 →+* R := ZMod.castHom (dvd_refl 3) R
  have hEF := map_commute f _ _ (prime_linear i)
  have hEQ := map_commute f _ _ (prime_mixed i)
  have hDF := map_commute f _ _ (prime_reverse_mixed i)
  have hDQ := map_commute f _ _ (prime_quadratic i)
  simp only [map_positiveLinear,map_positiveQuadratic] at hEF hEQ hDF hDQ
  exact polynomial_commute _ _ _ _ hEF hEQ hDF hDQ a b

theorem polynomial_two_short (a c : R) :
    polynomialRoot R 2 c * polynomialRoot R 0 a =
      polynomialRoot R 0 a * polynomialRoot R 2 c * polynomialRoot R 3 (-a*c) := by
  apply Matrix.mulVec_injective
  funext v
  simp only [←Matrix.mulVec_mulVec,polynomialRoot_apply,
    positiveAction_0,positiveAction_1,positiveAction_2,positiveAction_3,positiveAction_4,positiveAction_5]
  have hthree : (3:R)=0 := CharP.cast_eq_zero R 3
  funext x
  rcases x with i|i <;> fin_cases i
  · change (action2 R (c) (action0 R (a) (v))) (pos 0)=(action0 R (a) (action2 R (c) (action3 R (-a*c) (v)))) (pos 0)
    simp only [action0_pos0,action0_pos1,action0_pos2,action0_pos3,action0_neg0,action0_neg1,action0_neg2,action0_neg3,action2_pos0,action2_pos1,action2_pos2,action2_pos3,action2_neg0,action2_neg1,action2_neg2,action2_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action3_neg0,action3_neg1,action3_neg2,action3_neg3]
    linear_combination (a*c*(a*c*v (neg 0)+v (pos 3)+v (neg 3))) * hthree
  · change (action2 R (c) (action0 R (a) (v))) (pos 1)=(action0 R (a) (action2 R (c) (action3 R (-a*c) (v)))) (pos 1)
    simp only [action0_pos0,action0_pos1,action0_pos2,action0_pos3,action0_neg0,action0_neg1,action0_neg2,action0_neg3,action2_pos0,action2_pos1,action2_pos2,action2_pos3,action2_neg0,action2_neg1,action2_neg2,action2_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action3_neg0,action3_neg1,action3_neg2,action3_neg3]
    linear_combination (a*c*(c*v (neg 0)+v (neg 2))) * hthree
  · change (action2 R (c) (action0 R (a) (v))) (pos 2)=(action0 R (a) (action2 R (c) (action3 R (-a*c) (v)))) (pos 2)
    simp only [action0_pos0,action0_pos1,action0_pos2,action0_pos3,action0_neg0,action0_neg1,action0_neg2,action0_neg3,action2_pos0,action2_pos1,action2_pos2,action2_pos3,action2_neg0,action2_neg1,action2_neg2,action2_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action3_neg0,action3_neg1,action3_neg2,action3_neg3]
    linear_combination (-a*c*(a*v (neg 0)+v (neg 1))) * hthree
  · change (action2 R (c) (action0 R (a) (v))) (pos 3)=(action0 R (a) (action2 R (c) (action3 R (-a*c) (v)))) (pos 3)
    simp only [action0_pos0,action0_pos1,action0_pos2,action0_pos3,action0_neg0,action0_neg1,action0_neg2,action0_neg3,action2_pos0,action2_pos1,action2_pos2,action2_pos3,action2_neg0,action2_neg1,action2_neg2,action2_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action3_neg0,action3_neg1,action3_neg2,action3_neg3]
    linear_combination (-a*c*v (neg 0)) * hthree
  · change (action2 R (c) (action0 R (a) (v))) (neg 0)=(action0 R (a) (action2 R (c) (action3 R (-a*c) (v)))) (neg 0)
    simp only [action0_pos0,action0_pos1,action0_pos2,action0_pos3,action0_neg0,action0_neg1,action0_neg2,action0_neg3,action2_pos0,action2_pos1,action2_pos2,action2_pos3,action2_neg0,action2_neg1,action2_neg2,action2_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action3_neg0,action3_neg1,action3_neg2,action3_neg3] <;> ring
  · change (action2 R (c) (action0 R (a) (v))) (neg 1)=(action0 R (a) (action2 R (c) (action3 R (-a*c) (v)))) (neg 1)
    simp only [action0_pos0,action0_pos1,action0_pos2,action0_pos3,action0_neg0,action0_neg1,action0_neg2,action0_neg3,action2_pos0,action2_pos1,action2_pos2,action2_pos3,action2_neg0,action2_neg1,action2_neg2,action2_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action3_neg0,action3_neg1,action3_neg2,action3_neg3] <;> ring
  · change (action2 R (c) (action0 R (a) (v))) (neg 2)=(action0 R (a) (action2 R (c) (action3 R (-a*c) (v)))) (neg 2)
    simp only [action0_pos0,action0_pos1,action0_pos2,action0_pos3,action0_neg0,action0_neg1,action0_neg2,action0_neg3,action2_pos0,action2_pos1,action2_pos2,action2_pos3,action2_neg0,action2_neg1,action2_neg2,action2_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action3_neg0,action3_neg1,action3_neg2,action3_neg3] <;> ring
  · change (action2 R (c) (action0 R (a) (v))) (neg 3)=(action0 R (a) (action2 R (c) (action3 R (-a*c) (v)))) (neg 3)
    simp only [action0_pos0,action0_pos1,action0_pos2,action0_pos3,action0_neg0,action0_neg1,action0_neg2,action0_neg3,action2_pos0,action2_pos1,action2_pos2,action2_pos3,action2_neg0,action2_neg1,action2_neg2,action2_neg3,action3_pos0,action3_pos1,action3_pos2,action3_pos3,action3_neg0,action3_neg1,action3_neg2,action3_neg3]
    linear_combination (-a*c*v (neg 0)) * hthree

theorem polynomial_four_long (b c : R) :
    polynomialRoot R 4 c * polynomialRoot R 1 b =
      polynomialRoot R 1 b * polynomialRoot R 4 c * polynomialRoot R 5 (b*c) := by
  apply Matrix.mulVec_injective
  funext v
  simp only [←Matrix.mulVec_mulVec,polynomialRoot_apply,
    positiveAction_0,positiveAction_1,positiveAction_2,positiveAction_3,positiveAction_4,positiveAction_5]
  funext x
  rcases x with i|i <;> fin_cases i
  · change (action4 R (c) (action1 R (b) (v))) (pos 0)=(action1 R (b) (action4 R (c) (action5 R (b*c) (v)))) (pos 0)
    simp only [action1_pos0,action1_pos1,action1_pos2,action1_pos3,action1_neg0,action1_neg1,action1_neg2,action1_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3] <;> ring
  · change (action4 R (c) (action1 R (b) (v))) (pos 1)=(action1 R (b) (action4 R (c) (action5 R (b*c) (v)))) (pos 1)
    simp only [action1_pos0,action1_pos1,action1_pos2,action1_pos3,action1_neg0,action1_neg1,action1_neg2,action1_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3] <;> ring
  · change (action4 R (c) (action1 R (b) (v))) (pos 2)=(action1 R (b) (action4 R (c) (action5 R (b*c) (v)))) (pos 2)
    simp only [action1_pos0,action1_pos1,action1_pos2,action1_pos3,action1_neg0,action1_neg1,action1_neg2,action1_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3] <;> ring
  · change (action4 R (c) (action1 R (b) (v))) (pos 3)=(action1 R (b) (action4 R (c) (action5 R (b*c) (v)))) (pos 3)
    simp only [action1_pos0,action1_pos1,action1_pos2,action1_pos3,action1_neg0,action1_neg1,action1_neg2,action1_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3] <;> ring
  · change (action4 R (c) (action1 R (b) (v))) (neg 0)=(action1 R (b) (action4 R (c) (action5 R (b*c) (v)))) (neg 0)
    simp only [action1_pos0,action1_pos1,action1_pos2,action1_pos3,action1_neg0,action1_neg1,action1_neg2,action1_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3] <;> ring
  · change (action4 R (c) (action1 R (b) (v))) (neg 1)=(action1 R (b) (action4 R (c) (action5 R (b*c) (v)))) (neg 1)
    simp only [action1_pos0,action1_pos1,action1_pos2,action1_pos3,action1_neg0,action1_neg1,action1_neg2,action1_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3] <;> ring
  · change (action4 R (c) (action1 R (b) (v))) (neg 2)=(action1 R (b) (action4 R (c) (action5 R (b*c) (v)))) (neg 2)
    simp only [action1_pos0,action1_pos1,action1_pos2,action1_pos3,action1_neg0,action1_neg1,action1_neg2,action1_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3] <;> ring
  · change (action4 R (c) (action1 R (b) (v))) (neg 3)=(action1 R (b) (action4 R (c) (action5 R (b*c) (v)))) (neg 3)
    simp only [action1_pos0,action1_pos1,action1_pos2,action1_pos3,action1_neg0,action1_neg1,action1_neg2,action1_neg3,action4_pos0,action4_pos1,action4_pos2,action4_pos3,action4_neg0,action4_neg1,action4_neg2,action4_neg3,action5_pos0,action5_pos1,action5_pos2,action5_pos3,action5_neg0,action5_neg1,action5_neg2,action5_neg3] <;> ring

theorem positive_pair_commute (K : Type) [Field K] [CharP K 3]
    (i : Fin 6) (a b : K) :
    Commute (positiveRoot K (commutingPair i).1 a)
      (positiveRoot K (commutingPair i).2 b) := by
  change _ * _ = _ * _
  apply Units.ext
  simp only [Units.val_mul,positiveRoot_val]
  exact (polynomial_pair_commute K i a b).eq

theorem positive_two_short (K : Type) [Field K] [CharP K 3] (a c : K) :
    positiveRoot K 2 c * positiveRoot K 0 a =
      positiveRoot K 0 a * positiveRoot K 2 c * positiveRoot K 3 (-a*c) := by
  apply Units.ext
  simp only [Units.val_mul,positiveRoot_val]
  exact polynomial_two_short K a c

theorem positive_four_long (K : Type) [Field K] [CharP K 3] (b c : K) :
    positiveRoot K 4 c * positiveRoot K 1 b =
      positiveRoot K 1 b * positiveRoot K 4 c * positiveRoot K 5 (b*c) := by
  apply Units.ext
  simp only [Units.val_mul,positiveRoot_val]
  exact polynomial_four_long K b c

end SymmetricSubgroupAsymptotics.CFSGGTwoSimpleHigherCollecting
