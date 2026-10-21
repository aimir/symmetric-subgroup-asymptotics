import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialElements

/-! Sparse matrices of the literal initial D roots. The transported fork
is proved to be the two-entry root e1+e_last (and its transpose), including
its coefficient signs. No ambient coordinate permutation is assumed to
belong to D without its previously proved signed SL lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialRootMatrices
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDGenerationSignedPermutation CFSGOrthogonalDGenerationMonomialAction
variable (K : Type) [Field K]

theorem second_ne_zero (s : ℕ) : second s ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change 1 = 0 at hv
  omega

theorem pen_ne_zero (s : ℕ) : pen (s + 2) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change s + 2 = 0 at hv
  omega

theorem last_ne_zero (s : ℕ) : last (s + 2) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change s + 3 = 0 at hv
  omega

theorem second_ne_pen (s : ℕ) : second s ≠ pen (s + 2) := by
  intro h
  have hv := congrArg Fin.val h
  change 1 = s + 2 at hv
  omega

theorem second_ne_last (s : ℕ) : second s ≠ last (s + 2) := by
  intro h
  have hv := congrArg Fin.val h
  change 1 = s + 3 at hv
  omega

theorem initialShortRoot_coe (s : ℕ) (a : K) :
    ((initialShortRoot K s a).val : Mat K (s + 4)) =
      1 + Matrix.single (Sum.inl (second s)) (Sum.inl (0 : Fin (s + 4))) a -
        Matrix.single (Sum.inr (0 : Fin (s + 4))) (Sum.inr (second s)) a := by
  change 1 + a • negative K (s + 4) 0 = _
  have hi : (0 : Fin (s + 4)).val + 1 < s + 4 := by change 0 + 1 < s + 4; omega
  have hn : (⟨(0 : Fin (s + 4)).val + 1, hi⟩ : Fin (s + 4)) = second s := rfl
  rw [negative, positive, dif_pos hi, hn]
  simp only [Matrix.transpose_sub, Matrix.transpose_single, smul_sub,
    Matrix.smul_single, smul_eq_mul, mul_one]
  abel

theorem forkRoot_coe (s : ℕ) (neg : Bool) (a : K) :
    ((rootElement K (s + 4) neg (last (s + 2)) a).val : Mat K (s + 4)) =
      if neg then
        1 + Matrix.single (Sum.inr (last (s + 2))) (Sum.inl (pen (s + 2))) a -
          Matrix.single (Sum.inr (pen (s + 2))) (Sum.inl (last (s + 2))) a
      else
        1 + Matrix.single (Sum.inl (pen (s + 2))) (Sum.inr (last (s + 2))) a -
          Matrix.single (Sum.inl (last (s + 2))) (Sum.inr (pen (s + 2))) a := by
  have hp : previous (s + 4) (last (s + 2)) = pen (s + 2) := by
    apply Fin.ext
    dsimp [previous, last, pen]
  have hi : ¬(last (s + 2)).val + 1 < s + 4 := by dsimp [last]; omega
  cases neg <;>
    change 1 + a • rootMatrix K (s + 4) _ (last (s + 2)) = _ <;>
    simp only [rootMatrix, Bool.false_eq_true, if_false, if_true, negative,
      positive, dif_neg hi, hp, Matrix.transpose_sub, Matrix.transpose_single,
      smul_sub, Matrix.smul_single, smul_eq_mul, mul_one] <;> abel

theorem initialStarRoot_coe (s : ℕ) (neg : Bool) (a : K) :
    ((initialStarRoot K s neg a).val : Mat K (s + 4)) =
      if neg then
        1 + Matrix.single (Sum.inr (last (s + 2))) (Sum.inl (second s)) a -
          Matrix.single (Sum.inr (second s)) (Sum.inl (last (s + 2))) a
      else
        1 + Matrix.single (Sum.inl (second s)) (Sum.inr (last (s + 2))) a -
          Matrix.single (Sum.inl (last (s + 2))) (Sum.inr (second s)) a := by
  let σ := Equiv.sumCongr (starPermutation s) (starPermutation s)
  let d : Index (s + 4) → K := Sum.elim (weight K (0 : Fin (s + 4)) (starPermutation s))
    (weight K (0 : Fin (s + 4)) (starPermutation s))
  have hW : ((starTransport K s).val : Mat K (s + 4)) =
      CFSGTypeAMonomialMatrices.monomial σ d :=
    signedPermutationElement_coe K (s + 4) 0 (starPermutation s)
  have hs (x : Fin (s + 4)) (hx : x ≠ second s) (hp : x ≠ pen (s + 2)) :
      starPermutation s x = x := by
    simp [starPermutation, Equiv.swap_apply_def, hx, hp]
  have hσ : (starPermutation s).symm = starPermutation s := by simp [starPermutation]
  have hl := hs (last (s + 2)) (Ne.symm (second_ne_last s)) (Ne.symm (pen_ne_last (s + 2)))
  have hlast : Equiv.swap (second s) (pen (s + 2)) (last (s + 2)) = last (s + 2) :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm (second_ne_last s)) (Ne.symm (pen_ne_last (s + 2)))
  change ((starTransport K s).val : Mat K (s + 4)) *
    ((rootElement K (s + 4) neg (last (s + 2)) a).val : Mat K (s + 4)) *
      (↑((starTransport K s).val⁻¹) : Mat K (s + 4)) = _
  rw [forkRoot_coe]
  cases neg
  · have h := conjugation_two_entry (starTransport K s).val σ d hW
      (Sum.inl (pen (s + 2))) (Sum.inr (last (s + 2)))
      (Sum.inl (last (s + 2))) (Sum.inr (pen (s + 2))) a
      (by simp [σ, d, hσ, hl, weight, last_ne_zero])
      (by simp [σ, d, starPermutation, weight, second_ne_zero])
    simpa [σ, d, hσ, hl, starPermutation, hlast, weight, second_ne_zero, last_ne_zero] using h
  · have h := conjugation_two_entry (starTransport K s).val σ d hW
      (Sum.inr (last (s + 2))) (Sum.inl (pen (s + 2)))
      (Sum.inr (pen (s + 2))) (Sum.inl (last (s + 2))) a
      (by simp [σ, d, starPermutation, weight, second_ne_zero])
      (by simp [σ, d, hσ, hl, weight, last_ne_zero])
    simpa [σ, d, hσ, hl, starPermutation, hlast, weight, second_ne_zero, last_ne_zero] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialRootMatrices
