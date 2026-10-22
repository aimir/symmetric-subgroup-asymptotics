import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeterCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationMonomialShortAction

/-! Full quadratic short-root transport by the actual B Coxeter word.
The middle-coordinate minus sign is retained in the parameter; opposite
signed coordinates have equal column signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeterShortAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationCoxeter CFSGOrthogonalBGenerationCoxeterCoordinates
open CFSGOrthogonalBGenerationSignedPermutation CFSGOrthogonalBGenerationMonomialShortAction
variable (K : Type) [Field K]

theorem coxeterSign_middle (r : ℕ) : coxeterSign K r (middle (r + 1)) = -1 := by
  simp [coxeterSign, terminalSign, terminalPermutation, prefixWeight, prefixRowPermutation,
    naturalPermutation, naturalWeight, Equiv.swap_apply_def, pos,
    CFSGOrthogonalBSerreMatrices.neg, middle]

theorem coxeterSign_paired (r : ℕ) (b : Fin (r + 1) ⊕ Fin (r + 1)) :
    coxeterSign K r (Sum.inl (paired (r + 1) b)) = coxeterSign K r (Sum.inl b) := by
  rcases b with (i | i)
  all_goals by_cases hi : i = Fin.last r
  all_goals simp [coxeterSign, terminalSign, terminalPermutation, prefixWeight, prefixRowPermutation,
    naturalPermutation, naturalWeight, Equiv.swap_apply_def, paired, pos,
    CFSGOrthogonalBSerreMatrices.neg, middle, hi]

theorem coxeterSign_mul_self (r : ℕ) (x : Index (r + 1)) :
    coxeterSign K r x * coxeterSign K r x = 1 := by
  have ht : terminalSign K r x * terminalSign K r x = 1 := by
    unfold terminalSign
    split_ifs <;> simp
  have hp := naturalWeight_mul_self K (r + 1) 0 (finRotate (r + 1)).symm
    ((prefixRowPermutation r).symm (terminalPermutation r x))
  change prefixWeight K r _ * prefixWeight K r _ = 1 at hp
  unfold coxeterSign
  calc
    _ = (terminalSign K r x * terminalSign K r x) *
        (prefixWeight K r ((prefixRowPermutation r).symm (terminalPermutation r x)) *
          prefixWeight K r ((prefixRowPermutation r).symm (terminalPermutation r x))) := by ring
    _ = 1 := by rw [ht, hp, one_mul]

theorem coxeter_short_conjugation (r : ℕ) (b : Fin (r + 1) ⊕ Fin (r + 1)) (a : K) :
    (coxeterWeyl K r).val * shortUnit K (r + 1) b a * (coxeterWeyl K r).val⁻¹ =
      shortUnit K (r + 1) (CFSGSymplecticSerreMatrices.coxeterCycle r b)
        ((-coxeterSign K r (Sum.inl b)) * a) := by
  let σ := (coxeterCycle r).symm
  let d := coxeterSign K r ∘ (coxeterCycle r).symm
  have hmInv : (coxeterCycle r).symm (middle (r + 1)) = middle (r + 1) := by
    apply (coxeterCycle r).injective
    simp only [Equiv.apply_symm_apply, cycle_middle]
  have hdm : d (middle (r + 1)) = -1 := by
    simp only [d, Function.comp_apply, hmInv, coxeterSign_middle]
  have hs (z : Index (r + 1)) : d (σ.symm z) = coxeterSign K r z := by
    simp only [d, σ, Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  apply short_conjugation (coxeterWeyl K r).val σ d (coxeter_monomial K r) b
    (CFSGSymplecticSerreMatrices.coxeterCycle r b) (-coxeterSign K r (Sum.inl b)) a
  · exact cycle_middle r
  · exact cycle_spatial r b
  · change coxeterCycle r (Sum.inl (paired (r + 1) b)) = _
    rw [cycle_spatial, spatial_cycle_paired]
  · rw [hdm]
    exact neg_ne_zero.mpr one_ne_zero
  · rw [hs]
    exact coxeterSign_ne_zero K r _
  · rw [hs, hdm]
    ring
  · rw [hdm, hs, coxeterSign_paired]
    rw [neg_mul, coxeterSign_mul_self]

theorem full_short_line_transfer (r : ℕ) (H : Subgroup (Mat K (r + 1))ˣ)
    (hW : (coxeterWeyl K r).val ∈ H) (b : Fin (r + 1) ⊕ Fin (r + 1))
    (hB : ∀ a, shortUnit K (r + 1) b a ∈ H) :
    ∀ a, shortUnit K (r + 1) (CFSGSymplecticSerreMatrices.coxeterCycle r b) a ∈ H := by
  intro a
  let l := -coxeterSign K r (Sum.inl b)
  have hll : l * l = 1 := by
    simpa only [l, neg_mul_neg] using coxeterSign_mul_self K r (Sum.inl b)
  have hh := H.mul_mem (H.mul_mem hW (hB (l * a))) (H.inv_mem hW)
  rw [coxeter_short_conjugation] at hh
  have he : l * (l * a) = a := by rw [← mul_assoc, hll, one_mul]
  simpa only [show (-coxeterSign K r (Sum.inl b)) * (l * a) = a from he] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeterShortAction
