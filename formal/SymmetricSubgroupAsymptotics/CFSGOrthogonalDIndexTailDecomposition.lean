import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailLinearExtension

/-! Literal head/tail decompositions in the original split coordinates.
These identities do not use an orthogonal-group or Witt decomposition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDSerreMatrices
variable (K : Type) [Field K]

theorem tailExtension_single (n : ℕ) (i : Index n) (a : K) :
    tailExtension K n (Pi.single i a) = Pi.single (tailIndex n i) a := by
  funext x
  obtain ⟨x, rfl⟩ := (tailEquiv n).surjective x
  rcases x with j | j
  · rw [tailEquiv_inl, tailExtension_tailIndex]
    simp only [Pi.single_apply, (tailIndex_injective n).eq_iff]
  · fin_cases j
    · change tailExtension K n (Pi.single i a) (Sum.inl (0 : Fin (n + 1))) =
        (Pi.single (tailIndex n i) a : Index (n + 1) → K) (Sum.inl 0)
      rw [tailExtension_positive_head]
      have hi : tailIndex n i ≠ Sum.inl (0 : Fin (n + 1)) := by
        intro h
        have hh : tailEquiv n (Sum.inl i) = tailEquiv n (Sum.inr 0) := h
        cases (tailEquiv n).injective hh
      simp only [Pi.single_apply, if_neg (Ne.symm hi)]
    · change tailExtension K n (Pi.single i a) (Sum.inr (0 : Fin (n + 1))) =
        (Pi.single (tailIndex n i) a : Index (n + 1) → K) (Sum.inr 0)
      rw [tailExtension_negative_head]
      have hi : tailIndex n i ≠ Sum.inr (0 : Fin (n + 1)) := by
        intro h
        have hh : tailEquiv n (Sum.inl i) = tailEquiv n (Sum.inr 1) := h
        cases (tailEquiv n).injective hh
      simp only [Pi.single_apply, if_neg (Ne.symm hi)]

theorem head_tail_decomposition (n : ℕ) (v : Index (n + 1) → K) :
    v = v (Sum.inl 0) • Pi.single (Sum.inl (0 : Fin (n + 1))) 1 +
      v (Sum.inr 0) • Pi.single (Sum.inr (0 : Fin (n + 1))) 1 +
      tailExtension K n (tailRestrictionLinear K n v) := by
  funext x
  rcases x with i | i
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        if_true, Sum.inl_ne_inr, if_false,
        tailExtension_positive_head, mul_one, mul_zero, add_zero]
    · change v (tailIndex n (Sum.inl j)) = _
      simp only [Pi.add_apply, Pi.smul_apply]
      have ht := tailExtension_tailIndex K n (tailRestrictionLinear K n v) (Sum.inl j)
      change tailExtension K n (tailRestrictionLinear K n v) (Sum.inl j.succ) = _ at ht
      rw [ht]
      simp [tailIndex, tailRestrictionLinear, tailRestriction]
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        if_true, Sum.inr_ne_inl, if_false,
        tailExtension_negative_head, mul_one, mul_zero, zero_add, add_zero]
    · change v (tailIndex n (Sum.inr j)) = _
      simp only [Pi.add_apply, Pi.smul_apply]
      have ht := tailExtension_tailIndex K n (tailRestrictionLinear K n v) (Sum.inr j)
      change tailExtension K n (tailRestrictionLinear K n v) (Sum.inr j.succ) = _ at ht
      rw [ht]
      simp [tailIndex, tailRestrictionLinear, tailRestriction]

theorem twice_head_tail_decomposition (n : ℕ) (v : Index (n + 2) → K)
    (h0 : v (Sum.inr 0) = 0) (h1 : v (Sum.inr (tailSecondIndex n)) = 0) :
    v = v (Sum.inl 0) • Pi.single (Sum.inl (0 : Fin (n + 2))) 1 +
      v (Sum.inl (tailSecondIndex n)) •
        Pi.single (Sum.inl (tailSecondIndex n)) 1 +
      twiceTailExtension K n (twiceTailRestriction K n v) := by
  have he := head_tail_decomposition K (n + 1) v
  have ht := head_tail_decomposition K n (tailRestrictionLinear K (n + 1) v)
  have ht0 : tailRestrictionLinear K (n + 1) v (Sum.inr 0) = 0 := h1
  have ht1 : tailRestrictionLinear K (n + 1) v (Sum.inl 0) =
      v (Sum.inl (tailSecondIndex n)) := rfl
  rw [ht0, zero_smul, add_zero, ht1] at ht
  rw [h0, zero_smul, add_zero, ht, map_add, map_smul, tailExtension_single] at he
  simpa only [twiceTailExtension, twiceTailRestriction, LinearMap.comp_apply,
    tailIndex, tailSecondIndex, add_assoc] using he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
