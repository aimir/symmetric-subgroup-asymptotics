import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPureRootCoverage
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTranspose

/-! Full paired-coordinate D root lines inside the literal elementary
subgroup. The checked signed-star transport provides last-coordinate
lines; chain commutators and transpose then supply every alternating
upper and lower block direction in all characteristics. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootLines
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDGenerationRootLineTransport CFSGOrthogonalDGenerationRootLineCommutators
open CFSGOrthogonalDGenerationSignedRootConjugation
open CFSGOrthogonalDGenerationPureStarCoverage CFSGOrthogonalDGenerationPureRootCoverage
open CFSGOrthogonalDIndexTranspose
variable (K : Type) [Field K]

private theorem actual_stars (s : ℕ) :
    ∀ side j, StarPair K s (elementaryRootGroup K (s + 4)) (column s side j) := by
  have hB : HasRootLine (elementaryRootGroup K (s + 4))
      (rootArray K (Sum.inl (second s)) (Sum.inr (last (s + 2)))) := by
    intro a
    refine ⟨(initialStarRoot K s false a).val, (initialStarRoot K s false a).property, ?_⟩
    exact initialStarRoot_coe K s false a
  have h0 := initial_star_pair K s (elementaryRootGroup K (s + 4))
    (coxeterWeyl K (s + 3)).property (fun a => (initialShortRoot K s a).property) hB
  exact all_stars K s (elementaryRootGroup K (s + 4))
    (coxeterWeyl K (s + 3)).property h0

theorem chain_line (s : ℕ) (i j : Fin (s + 4)) (hij : i ≠ j) :
    HasRootLine (elementaryRootGroup K (s + 4)) (chainArray i j) :=
  all_chain_lines K s _ (actual_stars K s) i j hij

private theorem plus_swap {r : ℕ} (i j : Fin r) (a : K) :
    plusArray j i a = plusArray i j (-a) := by
  ext x y
  simp only [plusArray, Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply]
  split_ifs <;> ring

private theorem plus_line_swap {r : ℕ} (H : Subgroup (Mat K r)ˣ)
    (i j : Fin r) (h : HasRootLine H (plusArray i j)) : HasRootLine H (plusArray j i) := by
  intro a
  obtain ⟨u, hu, he⟩ := h (-a)
  exact ⟨u, hu, he.trans (plus_swap K i j a).symm⟩

private theorem plus_last (s : ℕ) (i : Fin (s + 4)) (hi : i ≠ last (s + 2)) :
    HasRootLine (elementaryRootGroup K (s + 4)) (plusArray i (last (s + 2))) := by
  have hlt : i.val < s + 3 := by
    have hb := i.isLt
    have hn : i.val ≠ s + 3 := fun he => hi (Fin.ext he)
    omega
  exact (actual_stars K s false (⟨i.val, hlt⟩ : Fin (s + 3))).2

theorem plus_line (s : ℕ) (i j : Fin (s + 4)) (hij : i ≠ j) :
    HasRootLine (elementaryRootGroup K (s + 4)) (plusArray i j) := by
  by_cases hj : j = last (s + 2)
  · subst j
    exact plus_last K s i hij
  · by_cases hi : i = last (s + 2)
    · subst i
      exact plus_line_swap K _ j (last (s + 2)) (plus_last K s j hj)
    · exact chain_plus_lines _ i (last (s + 2)) j hi hij (Ne.symm hj)
        (chain_line K s i (last (s + 2)) hi)
        (plus_line_swap K _ j (last (s + 2)) (plus_last K s j hj))

theorem minus_line (s : ℕ) (i j : Fin (s + 4)) (hij : i ≠ j) :
    HasRootLine (elementaryRootGroup K (s + 4)) (minusArray i j) := by
  intro a
  obtain ⟨u, hu, he⟩ := plus_line K s i j hij a
  refine ⟨transposeUnit K (s + 4) u, transposeUnit_mem K (s + 4) u hu, ?_⟩
  change (u : Mat K (s + 4)).transpose = (plusArray i j a).transpose
  exact congrArg Matrix.transpose he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootLines
