import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPureStarCoverage
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootLineSymmetries

/-! Every original D simple-root parameter follows from the full
short line, initial star line and pure original Coxeter word. This is
coverage of the literal defining generators, not a full-orthogonal-group
identification or a finite-order comparison. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPureRootCoverage
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDGenerationRootLineTransport CFSGOrthogonalDGenerationRootLineCommutators
open CFSGOrthogonalDGenerationSignedRootConjugation CFSGOrthogonalDGenerationRootLineSymmetries
open CFSGOrthogonalDGenerationPureStarCoverage
variable (K : Type) [Field K]

theorem all_chain_lines (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hstars : ∀ side j, StarPair K s H (column s side j))
    (i j : Fin (s + 4)) (hij : i ≠ j) : HasRootLine H (chainArray i j) := by
  by_cases hi : i = last (s + 2)
  · subst i
    have hj : j.val < s + 3 := by
      have hb := j.isLt
      have hn : j.val ≠ s + 3 := fun he => hij (Fin.ext he).symm
      omega
    have hn := (hstars true (⟨j.val, hj⟩ : Fin (s + 3))).2
    change HasRootLine H (rootArray K (Sum.inr j) (Sum.inr (last (s + 2)))) at hn
    exact paired_line_transfer K H _ _ hn
  · have hi' : i.val < s + 3 := by
      have hb := i.isLt
      have hn : i.val ≠ s + 3 := fun he => hi (Fin.ext he)
      omega
    have hleft := (hstars false (⟨i.val, hi'⟩ : Fin (s + 3))).1
    change HasRootLine H (chainArray i (last (s + 2))) at hleft
    by_cases hj : j = last (s + 2)
    · subst j
      exact hleft
    · have hj' : j.val < s + 3 := by
        have hb := j.isLt
        have hn : j.val ≠ s + 3 := fun he => hj (Fin.ext he)
        omega
      have hp := (hstars false (⟨i.val, hi'⟩ : Fin (s + 3))).2
      change HasRootLine H (plusArray i (last (s + 2))) at hp
      have hn0 := (hstars true (⟨j.val, hj'⟩ : Fin (s + 3))).1
      change HasRootLine H (rootArray K (Sum.inr j) (Sum.inl (last (s + 2)))) at hn0
      have hn := paired_line_transfer K H _ _ hn0
      change HasRootLine H (rootArray K (Sum.inr (last (s + 2))) (Sum.inl j)) at hn
      have hm : HasRootLine H (minusArray j (last (s + 2))) := by
        intro a
        obtain ⟨g, hg, he⟩ := hn a
        exact ⟨g, hg, he.trans (minusArray_eq_rootArray K j (last (s + 2)) a).symm⟩
      exact plus_minus_lines H i j (last (s + 2)) hij hi hj hp hm

theorem chain_root_array (s : ℕ) (neg : Bool) (i : Fin (s + 4))
    (hi : i.val + 1 < s + 4) (a : K) :
    ((rootElement K (s + 4) neg i a).val : Mat K (s + 4)) =
      if neg then chainArray (⟨i.val + 1, hi⟩ : Fin (s + 4)) i a
      else chainArray i (⟨i.val + 1, hi⟩ : Fin (s + 4)) a := by
  cases neg <;>
    change 1 + a • rootMatrix K (s + 4) _ i = _ <;>
    simp only [rootMatrix, Bool.false_eq_true, if_false, if_true, negative,
      positive, dif_pos hi, Matrix.transpose_sub, Matrix.transpose_single,
      smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, chainArray] <;> abel

theorem all_roots_mem (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hstars : ∀ side j, StarPair K s H (column s side j))
    (neg : Bool) (i : Fin (s + 4)) (a : K) : (rootElement K (s + 4) neg i a).val ∈ H := by
  by_cases hi : i.val + 1 < s + 4
  · let j : Fin (s + 4) := ⟨i.val + 1, hi⟩
    have hij : i ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = i.val + 1 at hv
      omega
    cases neg
    · exact unit_mem_of_line K H _ (all_chain_lines K s H hstars i j hij)
        (rootElement K (s + 4) false i a).val a (chain_root_array K s false i hi a)
    · exact unit_mem_of_line K H _ (all_chain_lines K s H hstars j i (Ne.symm hij))
        (rootElement K (s + 4) true i a).val a (chain_root_array K s true i hi a)
  · have he : i = last (s + 2) := by
      apply Fin.ext
      have hb := i.isLt
      change i.val = s + 3
      omega
    subst i
    have hp := (hstars false (Fin.last (s + 2))).2
    change HasRootLine H (plusArray (pen (s + 2)) (last (s + 2))) at hp
    have hn0 := (hstars true (Fin.last (s + 2))).1
    change HasRootLine H (rootArray K (Sum.inr (pen (s + 2))) (Sum.inl (last (s + 2)))) at hn0
    have hn := paired_line_transfer K H _ _ hn0
    change HasRootLine H (rootArray K (Sum.inr (last (s + 2))) (Sum.inl (pen (s + 2)))) at hn
    cases neg
    · exact unit_mem_of_line K H _ hp (rootElement K (s + 4) false (last (s + 2)) a).val a
        (forkRoot_coe K s false a)
    · apply unit_mem_of_line K H (minusArray (pen (s + 2)) (last (s + 2)))
        (by
          intro t
          obtain ⟨g, hg, he⟩ := hn t
          exact ⟨g, hg, he.trans (minusArray_eq_rootArray K (pen (s + 2)) (last (s + 2)) t).symm⟩)
        (rootElement K (s + 4) true (last (s + 2)) a).val a
      simpa only [minusArray, plusArray, Matrix.transpose_add, Matrix.transpose_sub,
        Matrix.transpose_one, Matrix.transpose_single] using forkRoot_coe K s true a

theorem elementary_le_of_root_lines (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hW : (coxeterWeyl K (s + 3)).val ∈ H)
    (hA : ∀ a, (initialShortRoot K s a).val ∈ H)
    (hB : HasRootLine H (rootArray K (Sum.inl (second s)) (Sum.inr (last (s + 2))))) :
    elementaryRootGroup K (s + 4) ≤ H := by
  have h0 := initial_star_pair K s H hW hA hB
  have hs := all_stars K s H hW h0
  apply (Subgroup.closure_le H).mpr
  rintro g ⟨neg, i, a, rfl⟩
  exact all_roots_mem K s H hs neg i a

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPureRootCoverage
