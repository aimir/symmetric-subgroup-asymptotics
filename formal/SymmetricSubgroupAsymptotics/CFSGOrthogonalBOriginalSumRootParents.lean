import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRootParents
import SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation
import SymmetricSubgroupAsymptotics.CFSGSerreSimpleRootLocalNilpotence

/-! Actual source parents for all positive long sum roots. Descent in
the SECOND index is a literal path suffix. At the terminal index the
first-root operator commutes through the terminal second divided power.
The final adjacent pair has parent coefficient TWO, from Lie skewness
and divided-power composition in the original source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalSumRootParents
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreLocalNilpotence
open CFSGOrthogonalBOriginalRootCandidates CFSGOrthogonalBOriginalRootParents
variable (r : ℕ)

theorem positive_sum_second_parent (i j : Fin r) (hj : j.val + 1 < r)
    (hij : i.val < j.val) :
    let next : Fin r := ⟨j.val + 1, hj⟩
    let child : Pair r := ⟨(i, j), hij⟩
    let parent : Pair r := ⟨(i, next), by dsimp [next]; omega⟩
    integralOperator (CartanMatrix.B r).transpose false j 1 (sumRoot r false parent) =
      sumRoot r false child := by
  dsimp only
  let last : Fin r := ⟨r - 1, by omega⟩
  let previous : Fin r := ⟨r - 2, by have hi := i.isLt; omega⟩
  have hs := descend_split r j last (by dsimp [last]; omega)
  simp only [sumRoot, map_smul]
  change (-1 : ℤ) • integralOperator _ false j 1 (path r false previous _) =
    (-1 : ℤ) • path r false previous _
  apply congrArg (fun x : Source r => (-1 : ℤ) • x)
  rw [hs]
  simp only [steps, List.map_append, List.map_cons, List.map_nil]
  rw [← List.append_assoc]
  exact (positive_path_snoc r previous _ j 1).symm

/-- At the terminal second index there is no trailing path. -/
theorem terminal_sum_eq_second (i last : Fin r) (hlast : last.val + 1 = r)
    (hilast : i.val < last.val) :
    sumRoot r false ⟨(i, last), hilast⟩ =
      (-1 : ℤ) • integralOperator (CartanMatrix.B r).transpose false last 2
        (difference r false ⟨(i, last), hilast⟩) := by
  have hlastIndex : (⟨r - 1, by have hl := last.isLt; omega⟩ : Fin r) = last := by
    apply Fin.ext
    change r - 1 = last.val
    omega
  have hprevious : (⟨last.val - 1, by have hl := last.isLt; omega⟩ : Fin r) =
      (⟨r - 2, by have hl := last.isLt; omega⟩ : Fin r) := by
    apply Fin.ext
    change last.val - 1 = r - 2
    omega
  simp only [sumRoot, hlastIndex, descend_self, steps, List.map_nil, List.append_nil,
    difference, hprevious]
  exact congrArg (fun x : Source r => (-1 : ℤ) • x)
    (positive_path_snoc r _ _ last 2)

theorem positive_sum_terminal_first_parent (i last : Fin r)
    (hlast : last.val + 1 = r) (hgap : i.val + 1 < last.val) :
    let next : Fin r := ⟨i.val + 1, by omega⟩
    let child : Pair r := ⟨(i, last), by change i.val < last.val; omega⟩
    let parent : Pair r := ⟨(next, last), hgap⟩
    integralOperator (CartanMatrix.B r).transpose false i 1 (sumRoot r false parent) =
      sumRoot r false child := by
  dsimp only
  have hi : i.val + 1 < r := by omega
  let next : Fin r := ⟨i.val + 1, hi⟩
  let child : Pair r := ⟨(i, last), by change i.val < last.val; omega⟩
  let parent : Pair r := ⟨(next, last), hgap⟩
  have hzero : (CartanMatrix.B r).transpose i last = 0 := by
    have hne : last ≠ i := by intro h; have hv := congrArg Fin.val h; omega
    have hnot1 : last.val + 1 ≠ i.val := by omega
    have hnot2 : i.val + 1 ≠ last.val := by omega
    simp [Matrix.transpose_apply, CartanMatrix.B, Matrix.of_apply, hne, hnot1, hnot2]
  have hc := CFSGSerreCrossNodeCommutation.integralOperators_commute_of_lie_zero
    (CartanMatrix.B r).transpose false false i last
    (CFSGSerreCrossNodeCommutation.rootVector_lie_zero_of_cartan_zero
      (CartanMatrix.B r).transpose false i last hzero) 1 2
  rw [terminal_sum_eq_second r next last hlast hgap,
    terminal_sum_eq_second r i last hlast (by omega), map_smul]
  apply congrArg (fun x : Source r => (-1 : ℤ) • x)
  have he := congrArg (fun D : Module.End ℤ (Source r) => D (difference r false parent)) hc.eq
  change integralOperator _ false i 1 (integralOperator _ false last 2
      (difference r false parent)) =
        integralOperator _ false last 2 (integralOperator _ false i 1
          (difference r false parent)) at he
  rw [he, positive_difference_parent r i last hgap]

/-- The adjacent terminal long root has the short-root parent with coefficient two. -/
theorem positive_adjacent_terminal_sum_parent (i last : Fin r)
    (hi : i.val + 1 = last.val) (hlast : last.val + 1 = r) :
    integralOperator (CartanMatrix.B r).transpose false last 1 (short r false i) =
      (2 : ℕ) • sumRoot r false ⟨(i, last), by change i.val < last.val; omega⟩ := by
  have hlastIndex : (⟨r - 1, by have hl := last.isLt; omega⟩ : Fin r) = last := by
    apply Fin.ext
    change r - 1 = last.val
    omega
  have hd : difference r false ⟨(i, last), by change i.val < last.val; omega⟩ =
      latticeGenerator (CartanMatrix.B r).transpose (.E i) := by
    have hs : (⟨last.val - 1, by have hl := last.isLt; omega⟩ : Fin r) = i :=
      by
        apply Fin.ext
        change last.val - 1 = i.val
        omega
    simp [difference, hs, descend_self, path, steps,
      CFSGSerreDividedPowerPaths.pathVector, CFSGSerreDividedPowerPaths.applySteps]
  have hshort : short r false i = integralOperator (CartanMatrix.B r).transpose false i 1
      (latticeGenerator (CartanMatrix.B r).transpose (.E last)) := by
    have hs : (⟨i.val + 1, by omega⟩ : Fin r) = last := Fin.ext hi
    have h := positive_short_parent r i (by omega)
    dsimp only at h
    rw [hs] at h
    simpa only [short, hlastIndex, descend_self, steps, List.map_nil, path,
      Bool.false_eq_true, if_false, one_smul, CFSGSerreDividedPowerPaths.pathVector,
      CFSGSerreDividedPowerPaths.applySteps] using h.symm
  have hskew : integralOperator (CartanMatrix.B r).transpose false last 1
      (latticeGenerator (CartanMatrix.B r).transpose (.E i)) = -short r false i := by
    rw [hshort]
    apply Subtype.ext
    simp only [integralOperator_one_coe_apply, LieAlgebra.ad_apply, Submodule.coe_neg]
    exact (lie_skew _ _).symm
  have hp := CFSGSerreDividedPowerPathComposition.path_double_step
    (CartanMatrix.B r).transpose false i [] last
  change integralOperator _ false last 1
    (integralOperator _ false last 1 (latticeGenerator _ (.E i))) =
      (2 : ℕ) • integralOperator _ false last 2 (latticeGenerator _ (.E i)) at hp
  rw [hskew, map_neg] at hp
  rw [terminal_sum_eq_second r i last hlast (by omega), hd]
  simpa only [neg_one_smul, two_nsmul, neg_add_rev, neg_neg] using congrArg Neg.neg hp

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalSumRootParents
