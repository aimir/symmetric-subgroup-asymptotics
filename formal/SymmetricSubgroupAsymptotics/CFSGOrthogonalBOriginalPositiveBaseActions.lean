import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveWeightIdentification

/-! Actual original-source base actions for B height induction. Cartan
raises and simple lowerings use only source Serre relations and literal
rational Cartan tails, with no source action-table hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveBaseActions
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights
open CFSGOrthogonalBOriginalRootCandidates CFSGOrthogonalBOriginalPositiveSourceProfile
open CFSGOrthogonalBUniformPositiveTables
open CFSGOrthogonalBOriginalPositivePrimitiveFamily
variable (r : ℕ)

theorem cartan_mem (i : Fin r) : generator (CartanMatrix.B r).transpose (.H i) ∈ span r := by
  by_cases hi : i.val + 1 < r
  · rw [CFSGOrthogonalBOriginalRationalCartanTail.nonterminal_generator_H r i hi]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨.inl i, rfl⟩)
      (Submodule.subset_span ⟨.inl ⟨i.val + 1, hi⟩, rfl⟩)
  · rw [CFSGOrthogonalBOriginalRationalCartanTail.terminal_generator_H r i hi]
    exact Submodule.smul_mem _ 2 (Submodule.subset_span ⟨.inl i, rfl⟩)

theorem simple_occurs (i : Fin r) : ∃ j : PositiveIndex r,
    height r j = 1 ∧ CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j =
      rootVector (CartanMatrix.B r).transpose false i := by
  by_cases hi : i.val + 1 < r
  · let next : Fin r := ⟨i.val + 1, hi⟩
    let ij : Pair r := ⟨(i, next), by dsimp [next]; omega⟩
    refine ⟨.inr (.inl ij), ?_, ?_⟩
    · simp [height, rootHeight, ij, next]
    · simp [CFSGOrthogonalBOriginalPositivePrimitiveFamily.source, root, difference,
        path, steps, descend, ij, next, CFSGSerreDividedPowerPaths.pathVector,
        CFSGSerreDividedPowerPaths.applySteps, CFSGSerreDiagram.latticeGenerator,
        CFSG.Models.Chevalley.rootVector]
  · refine ⟨.inr (.inr (.inl i)), ?_, ?_⟩
    · change r - i.val = 1
      have hlt := i.isLt
      omega
    · have hl : (⟨r - 1, by have hlt := i.isLt; omega⟩ : Fin r) = i := by
        apply Fin.ext
        change r - 1 = i.val
        have hlt := i.isLt
        omega
      simp [CFSGOrthogonalBOriginalPositivePrimitiveFamily.source, root, short, hl,
        descend_self, steps, path, CFSGSerreDividedPowerPaths.pathVector,
        CFSGSerreDividedPowerPaths.applySteps, CFSGSerreDiagram.latticeGenerator,
        CFSG.Models.Chevalley.rootVector]

theorem simple_mem (i : Fin r) : rootVector (CartanMatrix.B r).transpose false i ∈ span r := by
  obtain ⟨j, hj, he⟩ := simple_occurs r i
  rw [← he]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem height_one_simple (j : PositiveIndex r) (hj : height r j = 1) :
    ∃ i : Fin r, CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j =
      rootVector (CartanMatrix.B r).transpose false i := by
  rcases j with b | (ij | (i | ij))
  · simp [height] at hj
  · have hh := ij.property
    have hn : ij.val.2.val = ij.val.1.val + 1 := by
      simp only [height, rootHeight] at hj
      omega
    have hs : (⟨ij.val.2.val - 1, by have h := ij.val.2.isLt; omega⟩ : Fin r) = ij.val.1 := by
      apply Fin.ext
      change ij.val.2.val - 1 = ij.val.1.val
      omega
    refine ⟨ij.val.1, ?_⟩
    simp [CFSGOrthogonalBOriginalPositivePrimitiveFamily.source, root, difference,
      hs, descend_self, steps, path, CFSGSerreDividedPowerPaths.pathVector,
      CFSGSerreDividedPowerPaths.applySteps, CFSGSerreDiagram.latticeGenerator,
      CFSG.Models.Chevalley.rootVector]
  · have hi := i.isLt
    have hn : r - 1 = i.val := by simp only [height, rootHeight] at hj; omega
    have hs : (⟨r - 1, by omega⟩ : Fin r) = i := Fin.ext hn
    refine ⟨i, ?_⟩
    simp [CFSGOrthogonalBOriginalPositivePrimitiveFamily.source, root, short,
      hs, descend_self, steps, path, CFSGSerreDividedPowerPaths.pathVector,
      CFSGSerreDividedPowerPaths.applySteps, CFSGSerreDiagram.latticeGenerator,
      CFSG.Models.Chevalley.rootVector]
  · have hi := ij.val.1.isLt
    have hk := ij.val.2.isLt
    have hij := ij.property
    simp only [height, rootHeight] at hj
    omega

theorem raising_base (i : Fin r) (j : PositiveIndex r) (hj : height r j = 0) :
    ⁅rootVector (CartanMatrix.B r).transpose false i,
      CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j⁆ =
      Fintype.linearCombination ℚ (CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r)
        (raising r i j) := by
  apply raising_of_mem
  cases j with
  | inr j => have hp := rootHeight_pos r j; change rootHeight r j = 0 at hj; omega
  | inl b =>
    change ⁅rootVector (CartanMatrix.B r).transpose false i,
      CFSGOrthogonalBOriginalRationalCartanTail.tail r b.val⁆ ∈ span r
    simp only [CFSGOrthogonalBOriginalRationalCartanTail.tail, lie_sum]
    apply Submodule.sum_mem
    intro a ha
    by_cases h : b.val + a < r
    · rw [CFSGOrthogonalBOriginalRationalCartanTail.Hhalf, dif_pos h, lie_smul]
      apply Submodule.smul_mem
      rw [← lie_skew (rootVector (CartanMatrix.B r).transpose false i)
        (generator (CartanMatrix.B r).transpose (.H ⟨b.val + a, h⟩))]
      have hHE : ⁅generator (CartanMatrix.B r).transpose (.H ⟨b.val + a, h⟩),
          rootVector (CartanMatrix.B r).transpose false i⁆ =
          ((CartanMatrix.B r).transpose ⟨b.val + a, h⟩ i : ℚ) •
            rootVector (CartanMatrix.B r).transpose false i :=
        coroot_root (CartanMatrix.B r).transpose false ⟨b.val + a, h⟩ i
      rw [hHE]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (simple_mem r i))
    · rw [CFSGOrthogonalBOriginalRationalCartanTail.Hhalf, dif_neg h, lie_zero]
      exact Submodule.zero_mem _

theorem lowering_base (a : Fin r) (j : PositiveIndex r) (hj : height r j = 1) :
    ⁅oppositeVector (CartanMatrix.B r).transpose false a,
      CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j⁆ =
      Fintype.linearCombination ℚ (CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r)
        (lowering r a j) := by
  apply lowering_of_mem
  obtain ⟨i, hi⟩ := height_one_simple r j hj
  rw [hi]
  by_cases ha : a = i
  · subst a
    rw [opposite_same]
    exact Submodule.neg_mem _ (cartan_mem r i)
  · rw [opposite_distinct (CartanMatrix.B r).transpose false a i ha]
    exact Submodule.zero_mem _

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveBaseActions
