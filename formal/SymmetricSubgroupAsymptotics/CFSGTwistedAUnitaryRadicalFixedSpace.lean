import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadical
import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace

/-! The literal all-q radical arrays fix exactly their first coordinate
line. This uses actual trace-solvable arrays, including characteristic2;
it does not assume that those arrays already lie in the derived source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [CommRing K] [Fintype J] [DecidableEq J]

theorem upperArray_mulVec_head (w v : J → K) (b : K) (x : Index J → K) :
    (upperArray w v b *ᵥ x) (.inl ()) =
      x (.inl ()) + dotProduct w (fun i => x (.inr (.inl i))) + b * x (.inr (.inr ())) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, upperArray, add_assoc]

theorem upperArray_mulVec_middle (w v : J → K) (b : K) (x : Index J → K) (i : J) :
    (upperArray w v b *ᵥ x) (.inr (.inl i)) =
      x (.inr (.inl i)) + v i * x (.inr (.inr ())) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, upperArray, ite_mul]

theorem upperArray_mulVec_last (w v : J → K) (b : K) (x : Index J → K) :
    (upperArray w v b *ᵥ x) (.inr (.inr ())) = x (.inr (.inr ())) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, upperArray]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists

theorem exists_nonzero_central_parameter (q : CFSG.PrimePower) (s : ℕ) :
    ∃ b : q.Extension 2, b ≠ 0 ∧ Condition q s 0 b := by
  rcases neg_one_pow_eq_or (q.Extension 2) s with hp | hp
  · obtain ⟨t, ht, hts⟩ := CFSGTwistedAQuadraticTrace.exists_skew_nonzero q
    refine ⟨t, ht, ?_⟩
    simp [Condition, parity, hp, hts, hermitianNorm]
  · refine ⟨1, one_ne_zero, ?_⟩
    simp [Condition, parity, hp, hermitianNorm]

theorem firstRow_zero (q : CFSG.PrimePower) (s : ℕ) : firstRow q s 0 = 0 := by
  have hz : definingFieldAutomorphism q 2 ∘ (0 : Fin (s + 1) → q.Extension 2) = 0 := by
    funext j
    exact map_zero (definingFieldAutomorphism q 2)
  funext i
  change -parity q s * ((definingFieldAutomorphism q 2 ∘
    (0 : Fin (s + 1) → q.Extension 2)) ᵥ* middleForm q s) i = 0
  rw [hz, Matrix.zero_vecMul]
  simp

theorem firstRow_single_dot (q : CFSG.PrimePower) (s : ℕ)
    (i : Fin (s + 1)) (z : Fin (s + 1) → q.Extension 2) :
    dotProduct (firstRow q s (Pi.single i 1)) z =
      -parity q s * (middleForm q s *ᵥ z) i := by
  simp [firstRow, radicalRow, Matrix.vecMul, Matrix.mulVec, dotProduct,
    Pi.single_apply, ite_mul, Finset.mul_sum, mul_assoc]

theorem radicalArrays_fixed_iff (q : CFSG.PrimePower) (s : ℕ)
    (x : Index (Fin (s + 1)) → q.Extension 2) :
    (∀ v b, Condition q s v b → upperArray (firstRow q s v) v b *ᵥ x = x) ↔
      (∀ i, x (.inr (.inl i)) = 0) ∧ x (.inr (.inr ())) = 0 := by
  constructor
  · intro hx
    obtain ⟨t, ht, htc⟩ := exists_nonzero_central_parameter q s
    have h0 := congrArg (fun y : Index (Fin (s + 1)) → q.Extension 2 => y (.inl ()))
      (hx 0 t htc)
    dsimp only at h0
    rw [upperArray_mulVec_head, firstRow_zero, zero_dotProduct, add_zero] at h0
    have hlast : x (.inr (.inr ())) = 0 :=
      (mul_eq_zero.mp (add_eq_left.mp h0)).resolve_left ht
    let z : Fin (s + 1) → q.Extension 2 := fun i => x (.inr (.inl i))
    have hzero : middleForm q s *ᵥ z = 0 := by
      funext i
      obtain ⟨b, hb⟩ := condition_exists q s (Pi.single i 1)
      have hi := congrArg (fun y : Index (Fin (s + 1)) → q.Extension 2 => y (.inl ()))
        (hx (Pi.single i 1) b hb)
      dsimp only at hi
      rw [upperArray_mulVec_head, hlast, mul_zero, add_zero] at hi
      change x (.inl ()) + dotProduct (firstRow q s (Pi.single i 1)) z = x (.inl ()) at hi
      rw [firstRow_single_dot] at hi
      have hp : -parity q s ≠ 0 := neg_ne_zero.mpr (pow_ne_zero s (neg_ne_zero.mpr one_ne_zero))
      exact (mul_eq_zero.mp (add_eq_left.mp hi)).resolve_left hp
    have hj : (signedReversalUnit (q.Extension 2) s : Mat (q.Extension 2) s) *ᵥ z = 0 := by
      change (-(signedReversalUnit (q.Extension 2) s : Mat (q.Extension 2) s)) *ᵥ z = 0 at hzero
      rw [Matrix.neg_mulVec] at hzero
      exact neg_eq_zero.mp hzero
    have hz : z = 0 := Matrix.mulVec_injective_of_isUnit
      (signedReversalUnit (q.Extension 2) s).isUnit (by simpa using hj)
    exact ⟨fun i => congrFun hz i, hlast⟩
  · rintro ⟨hm, hl⟩ v b _
    ext (u | (i | u))
    · cases u
      rw [upperArray_mulVec_head, hl]
      have hz : (fun i => x (.inr (.inl i))) = 0 := funext hm
      rw [hz, dotProduct_zero]
      ring
    · rw [upperArray_mulVec_middle, hl]
      ring
    · cases u
      exact upperArray_mulVec_last _ _ _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadical
