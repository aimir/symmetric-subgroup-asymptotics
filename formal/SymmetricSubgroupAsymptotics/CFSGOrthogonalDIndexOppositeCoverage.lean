import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexCoxeterOpposition
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexChainCompletion

/-! Positive U lines and the two actual Coxeter-image lines cover all
original D simple-root parameters. Only checked sparse commutators and
the original defining-generator closure are used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOppositeCoverage
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationRootArrays CFSGOrthogonalDGenerationRootLineTransport
open CFSGOrthogonalDGenerationRootLineCommutators CFSGOrthogonalDGenerationChainCommutators
open CFSGOrthogonalDGenerationRootLineSymmetries CFSGOrthogonalDGenerationPureRootCoverage
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDIndexOppositeRootLines CFSGOrthogonalDIndexCoxeterOpposition
open CFSGOrthogonalDIndexChainCompletion
variable (K : Type) [Field K]

private theorem line_mono {r : ℕ} (S H : Subgroup (Mat K r)ˣ) (hSH : S ≤ H)
    (A : K → Mat K r) (hA : HasRootLine S A) : HasRootLine H A := by
  intro a
  obtain ⟨g, hg, he⟩ := hA a
  exact ⟨g, hSH hg, he⟩

theorem elementary_le_of_U_and_coxeter_U (s : ℕ) (H : Subgroup (Mat K (s + 4))ˣ)
    (hU : ambientUnipotent K (s + 4) ≤ H)
    (hWU : (ambientUnipotent K (s + 4)).map
      (MulAut.conj (coxeterWeyl K (s + 3)).val).toMonoidHom ≤ H) :
    elementaryRootGroup K (s + 4) ≤ H := by
  obtain ⟨hcorner, hminus⟩ := coxeter_negative_lines K s H hWU
  have hpositive (i j : Fin (s + 4)) (hij : i < j) : HasRootLine H (chainArray i j) :=
    line_mono K _ H hU _ (positive_chain_line K (s + 4) i j hij)
  have hlast : (⟨s + 4 - 1, by omega⟩ : Fin (s + 4)) = Fin.last (s + 3) := by
    apply Fin.ext
    simp only [Fin.val_mk, Fin.val_last]
    omega
  have hchains : ∀ i j : Fin (s + 4), i ≠ j → HasRootLine H (chainArray i j) := by
    apply complete_of_positive_and_last_zero (s + 4) (by omega)
      (fun i j => HasRootLine H (chainArray i j)) hpositive
    · rw [hlast]
      exact hcorner
    · intro i j k hij hik hjk hi hj
      exact chain_chain_lines H i j k hij hik hjk hi hj
  have hpen0 : pen (s + 2) ≠ (0 : Fin (s + 4)) := by
    intro he
    have hv := congrArg Fin.val he
    change s + 2 = 0 at hv
    omega
  have hpenlast : pen (s + 2) ≠ last (s + 2) := by
    intro he
    have hv := congrArg Fin.val he
    change s + 2 = s + 3 at hv
    omega
  have h0last : (0 : Fin (s + 4)) ≠ last (s + 2) := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = s + 3 at hv
    omega
  have hmfork : HasRootLine H (minusArray (pen (s + 2)) (last (s + 2))) :=
    minus_chain_lines K H (pen (s + 2)) 0 (last (s + 2))
      hpen0 hpenlast h0last hminus (hchains 0 (pen (s + 2)) (Ne.symm hpen0))
  have hpfork : HasRootLine H (plusArray (pen (s + 2)) (last (s + 2))) :=
    line_mono K _ H hU _ (positive_plus_line K s _ _ hpenlast)
  apply (Subgroup.closure_le H).mpr
  rintro g ⟨neg, i, a, rfl⟩
  by_cases hi : i.val + 1 < s + 4
  · have hij : i ≠ (⟨i.val + 1, hi⟩ : Fin (s + 4)) := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = i.val + 1 at hv
      omega
    cases neg
    · exact unit_mem_of_line K H _ (hchains i _ hij) _ a (chain_root_array K s false i hi a)
    · exact unit_mem_of_line K H _ (hchains _ i (Ne.symm hij)) _ a (chain_root_array K s true i hi a)
  · have he : i = last (s + 2) := by
      apply Fin.ext
      have hb := i.isLt
      change i.val = s + 3
      omega
    subst i
    cases neg
    · exact unit_mem_of_line K H _ hpfork _ a (forkRoot_coe K s false a)
    · apply unit_mem_of_line K H _ hmfork _ a
      simpa only [minusArray, plusArray, Matrix.transpose_add, Matrix.transpose_sub,
        Matrix.transpose_one, Matrix.transpose_single] using forkRoot_coe K s true a

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOppositeCoverage
