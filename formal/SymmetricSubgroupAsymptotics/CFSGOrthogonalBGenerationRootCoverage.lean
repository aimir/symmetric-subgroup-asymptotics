import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationLongElements

/-! Full original B simple-root coverage from the proved signed short
root lines in odd characteristic. Each chain root is an actual short-root
commutator; terminal negative parameters retain their required minus sign. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationRootCoverage
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationShortCommutator CFSGOrthogonalBGenerationLongElements
variable (K : Type) [Field K]

private theorem longElement_mem (s : ℕ) (H : Subgroup (Mat K (s + 3))ˣ)
    (hShort : ∀ (b : Fin (s + 3) ⊕ Fin (s + 3)) (a : K), shortUnit K (s + 3) b a ∈ H)
    (b c : Fin (s + 3) ⊕ Fin (s + 3)) (a : K) :
    (longRootElement K (s + 2) b c a).val ∈ H :=
  H.mul_mem (H.mul_mem (H.mul_mem (hShort b a) (hShort c (-(2 : K)⁻¹)))
    (H.inv_mem (hShort b a))) (H.inv_mem (hShort c (-(2 : K)⁻¹)))

theorem elementary_le_of_all_short (h2 : (2 : K) ≠ 0) (s : ℕ)
    (H : Subgroup (Mat K (s + 3))ˣ)
    (hShort : ∀ (b : Fin (s + 3) ⊕ Fin (s + 3)) (a : K), shortUnit K (s + 3) b a ∈ H) :
    elementaryRootGroup K (s + 3) ≤ H := by
  apply (Subgroup.closure_le H).mpr
  rintro u ⟨sgn, i, a, rfl⟩
  by_cases hi : i.val + 1 < s + 3
  · let j : Fin (s + 3) := ⟨i.val + 1, hi⟩
    have hji : j ≠ i := by
      intro he
      have hv := congrArg Fin.val he
      change i.val + 1 = i.val at hv
      omega
    cases sgn
    · let v := longRootElement K (s + 2) (Sum.inl i) (Sum.inr j) a
      have hv : (v.val : Mat K (s + 3)) =
          1 + a • longArray K (s + 3) (Sum.inl i) (Sum.inr j) :=
        longRootElement_val K h2 (s + 2) _ _ (by intro he; cases he)
          (by change Sum.inl i ≠ Sum.inl j; exact fun he => hji.symm (Sum.inl.inj he)) a
      have hr : (rootTransvection K (s + 3) false i a : Mat K (s + 3)) =
          1 + a • longArray K (s + 3) (Sum.inl i) (Sum.inr j) := by
        simp only [rootTransvection_val, rootMatrix, rootSecond, Bool.false_eq_true, if_false,
          positive, positiveSecond, dif_pos hi, if_pos hi, smul_zero, add_zero]
        rfl
      have he : v.val = rootTransvection K (s + 3) false i a := Units.ext (hv.trans hr.symm)
      rw [← he]
      exact longElement_mem K s H hShort _ _ a
    · let v := longRootElement K (s + 2) (Sum.inl j) (Sum.inr i) a
      have hv : (v.val : Mat K (s + 3)) =
          1 + a • longArray K (s + 3) (Sum.inl j) (Sum.inr i) :=
        longRootElement_val K h2 (s + 2) _ _ (by intro he; cases he)
          (by change Sum.inl j ≠ Sum.inl i; exact fun he => hji (Sum.inl.inj he)) a
      have hr : (rootTransvection K (s + 3) true i a : Mat K (s + 3)) =
          1 + a • longArray K (s + 3) (Sum.inl j) (Sum.inr i) := by
        simp only [rootTransvection_val, rootMatrix, rootSecond, if_true,
          negative, negativeSecond, dif_pos hi, if_pos hi, smul_zero, add_zero]
        rfl
      have he : v.val = rootTransvection K (s + 3) true i a := Units.ext (hv.trans hr.symm)
      rw [← he]
      exact longElement_mem K s H hShort _ _ a
  · cases sgn
    · rw [terminal_positive K (s + 3) i hi a]
      exact hShort (Sum.inl i) a
    · rw [terminal_negative K (s + 3) i hi a]
      exact hShort (Sum.inr i) (-a)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationRootCoverage
