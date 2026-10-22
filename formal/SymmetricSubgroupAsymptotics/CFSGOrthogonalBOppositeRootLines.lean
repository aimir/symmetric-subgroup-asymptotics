import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOppositionMonomial
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentRoots

/-! The SAME actual B opposition sends each positive defining root line
onto its negative line. All polynomial short-root coefficients are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateFlip
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
open CFSGOrthogonalBGenerationElements CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalDGenerationMonomialAction
variable (K : Type) [Field K]

theorem opposition_chain_conjugation (r : ℕ) (i j : Fin (r+1)) (hij : i≠j) (a : K) :
    (opposition K r).val * (chainElement K (r+1) i j hij a).val *
        (opposition K r).val⁻¹ =
      (chainElement K (r+1) j i hij.symm (-a)).val := by
  apply Units.ext
  change ((opposition K r).val : Mat K (r+1)) *
      ((chainElement K (r+1) i j hij a).val : Mat K (r+1)) *
      (↑((opposition K r).val⁻¹) : Mat K (r+1)) =
    ((chainElement K (r+1) j i hij.symm (-a)).val : Mat K (r+1))
  rw [chainElement_val, chainElement_val]
  simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [← add_sub_assoc]
  rw [conjugation_two_entry (opposition K r).val (oppositionPermutation r)
    (oppositionWeight K r) (opposition_monomial K r) _ _ _ _ a
    (oppositionWeight_ne_zero K r _) (oppositionWeight_ne_zero K r _)]
  simp only [oppositionPermutation, oppositionWeight, Equiv.sumCongr_symm,
    Equiv.sumComm_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Equiv.sumComm_apply,
    Sum.map_inl, Sum.elim_inl]
  ext x y
  simp [Matrix.single]
  all_goals try split_ifs
  all_goals ring

theorem positive_mem_unipotent (r : ℕ) (i : Fin (r+1)) (a : K) :
    rootElement K (r+1) false i a ∈ unipotent K (r+1) := by
  by_cases hi : i.val+1<r+1
  · let j : Fin (r+1) := ⟨i.val+1,hi⟩
    have hij : i < j := by change i.val < i.val+1; omega
    have he : rootElement K (r+1) false i a =
        chainElement K (r+1) i j (ne_of_lt hij) a := by
      apply Subtype.ext
      apply Units.ext
      rw [chainElement_val]
      change 1+a • rootMatrix K (r+1) false i+a^2 • rootSecond K (r+1) false i = _
      simp only [rootMatrix, rootSecond, Bool.false_eq_true, if_false,
        positive, positiveSecond, dif_pos hi, if_pos hi, smul_zero, add_zero]
      rfl
    rw [he]
    exact chainElement_mem_unipotent K (r+1) i j hij a
  · have he : rootElement K (r+1) false i a = shortElement K r i a := by
      apply Subtype.ext
      exact terminal_positive K (r+1) i hi a
    rw [he]
    exact shortElement_mem_unipotent K r i a

def rootScale (r : ℕ) (i : Fin (r+1)) : K :=
  if i.val+1<r+1 then -1 else (-1)^(r+1)

theorem rootScale_square (r : ℕ) (i : Fin (r+1)) :
    rootScale K r i * rootScale K r i = 1 := by
  unfold rootScale
  split_ifs
  · simp
  · rw [← mul_pow]; simp

theorem opposition_conjugates_positive (r : ℕ) (i : Fin (r+1)) (a : K) :
    opposition K r * rootElement K (r+1) false i a * (opposition K r)⁻¹ =
      rootElement K (r+1) true i (rootScale K r i * a) := by
  by_cases hi : i.val+1<r+1
  · let j : Fin (r+1) := ⟨i.val+1,hi⟩
    have hij : i≠j := by intro h; have hh:=congrArg Fin.val h; dsimp [j] at hh; omega
    apply Subtype.ext
    change (opposition K r).val * rootTransvection K (r+1) false i a *
      (opposition K r).val⁻¹ = rootTransvection K (r+1) true i (rootScale K r i*a)
    have hp : rootTransvection K (r+1) false i a =
        (chainElement K (r+1) i j hij a).val := by
      apply Units.ext
      rw [rootTransvection_val, chainElement_val]
      simp only [rootMatrix, rootSecond, Bool.false_eq_true, if_false,
        positive, positiveSecond, dif_pos hi, if_pos hi, smul_zero, add_zero]
      rfl
    rw [hp, opposition_chain_conjugation]
    apply Units.ext
    rw [chainElement_val, rootTransvection_val]
    simp only [rootScale, if_pos hi, neg_one_mul, rootMatrix, rootSecond, if_true,
      negative, negativeSecond, dif_pos hi, smul_zero, add_zero]
    rfl
  · apply Subtype.ext
    change (opposition K r).val * rootTransvection K (r+1) false i a *
      (opposition K r).val⁻¹ = rootTransvection K (r+1) true i (rootScale K r i*a)
    rw [terminal_positive K (r+1) i hi a, terminal_negative K (r+1) i hi]
    rw [opposition_short_conjugation]
    simp only [rootScale, if_neg hi, Sum.swap_inl, neg_mul]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateFlip
