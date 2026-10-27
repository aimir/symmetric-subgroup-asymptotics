import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRationalFamily
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDRationalCartanReconstruction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDInvariantForm

/-! Literal hyperbolic-orthogonal block entries are determined by the
actual Cartan/root coordinates. This is a uniform rational calculation,
not a source faithfulness or model-recognition assertion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformGramCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformRationalFamily
variable (r : ℕ) (hr : 4 ≤ r)

def Orthogonal (M : Mat ℚ r) : Prop :=
  M∈skewAdjointMatricesLieSubalgebra (gram ℚ r)

theorem block_entries (M : Mat ℚ r) (hM : Orthogonal r M) (i j : Fin r) :
    M (.inr i) (.inr j)= -M (.inl j) (.inl i) ∧
    M (.inl i) (.inr j)= -M (.inl j) (.inr i) ∧
    M (.inr i) (.inl j)= -M (.inr j) (.inl i) := by
  rw [Orthogonal,mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule] at hM
  change M.transpose*gram ℚ r=gram ℚ r*(-M) at hM
  have hA:=congrArg (fun N : Mat ℚ r=>N (.inl i) (.inr j)) hM
  have hB:=congrArg (fun N : Mat ℚ r=>N (.inr i) (.inr j)) hM
  have hC:=congrArg (fun N : Mat ℚ r=>N (.inl i) (.inl j)) hM
  simp [gram,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.transpose_apply] at hA hB hC
  exact ⟨by linarith,by linarith,by linarith⟩

include hr in
theorem coordinates_injective (M N : Mat ℚ r) (hM : Orthogonal r M)
    (hN : Orthogonal r N) (h : coordinates r hr M=coordinates r hr N) : M=N := by
  have hd : diagonal r M=diagonal r N := by
    apply CFSGOrthogonalDRationalCartanReconstruction.coordinates_injective r hr
    funext i
    exact congrFun h (.inl i)
  have he (j : Bool×RootIndex r) :
      M (CFSGOrthogonalDUniformRootCoordinates.entry r j).1
        (CFSGOrthogonalDUniformRootCoordinates.entry r j).2=
      N (CFSGOrthogonalDUniformRootCoordinates.entry r j).1
        (CFSGOrthogonalDUniformRootCoordinates.entry r j).2 := congrFun h (.inr j)
  have hA (i j : Fin r) : M (.inl i) (.inl j)=N (.inl i) (.inl j) := by
    by_cases hij : i=j
    · subst j
      exact congrFun hd i
    · by_cases hij' : i.val < j.val
      · exact he (false,.inl ⟨(i,j),hij'⟩)
      · have hji : j.val < i.val := by
          have hn : i.val≠j.val := fun hv=>hij (Fin.ext hv)
          omega
        exact he (true,.inl ⟨(j,i),hji⟩)
  have hB (i j : Fin r) : M (.inl i) (.inr j)=N (.inl i) (.inr j) := by
    by_cases hij : i=j
    · subst j
      exact (orthogonal_opposite_entries_zero r M hM i).2.trans
        (orthogonal_opposite_entries_zero r N hN i).2.symm
    · by_cases hij' : i.val < j.val
      · exact he (false,.inr ⟨(i,j),hij'⟩)
      · have hji : j.val < i.val := by
          have hn : i.val≠j.val := fun hv=>hij (Fin.ext hv)
          omega
        rw [(block_entries r M hM i j).2.1,(block_entries r N hN i j).2.1]
        exact congrArg Neg.neg (he (false,.inr ⟨(j,i),hji⟩))
  have hC (i j : Fin r) : M (.inr i) (.inl j)=N (.inr i) (.inl j) := by
    by_cases hij : i=j
    · subst j
      exact (orthogonal_opposite_entries_zero r M hM i).1.trans
        (orthogonal_opposite_entries_zero r N hN i).1.symm
    · by_cases hji : j.val < i.val
      · exact he (true,.inr ⟨(j,i),hji⟩)
      · have hij' : i.val < j.val := by
          have hn : i.val≠j.val := fun hv=>hij (Fin.ext hv)
          omega
        rw [(block_entries r M hM i j).2.2,(block_entries r N hN i j).2.2]
        exact congrArg Neg.neg (he (true,.inr ⟨(i,j),hij'⟩))
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · rw [(block_entries r M hM i j).1,(block_entries r N hN i j).1,hA]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformGramCoordinates
