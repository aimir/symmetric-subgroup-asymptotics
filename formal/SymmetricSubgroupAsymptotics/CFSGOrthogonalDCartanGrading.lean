import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveWeightIdentification

/-! The actual D diagonal grading is a strictly positive rational
combination of the original simple Cartan matrix images. No faithfulness
or source-coordinate spanning is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanGrading
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformRationalFamily CFSGOrthogonalDUniformGramBasis
open CFSGOrthogonalDUniformRootGrading
variable (r : ℕ) (hr : 4 ≤ r)

def integerWeight (i : Fin r) : ℤ := (r:ℤ)-1-i.val

def coefficient (i : Fin r) : ℚ :=
  CFSGOrthogonalDCartanIntrinsicCoordinates.rationalCoordinates r hr (integerWeight r) i

private theorem weight_nonneg (i : Fin r) : 0 ≤ integerWeight r i := by
  have hi:=i.isLt
  unfold integerWeight
  omega

include hr in
private theorem sum_positive : 0 < ∑ i : Fin r,integerWeight r i := by
  let zero : Fin r:=⟨0,by omega⟩
  have hz : 0 < integerWeight r zero := by dsimp [integerWeight,zero];omega
  have hle := Finset.single_le_sum (f:=integerWeight r)
    (fun i _=>weight_nonneg r i) (Finset.mem_univ zero)
  omega

include hr in
private theorem last_zero : integerWeight r ⟨r-1,by omega⟩=0 := by
  unfold integerWeight
  rw [Nat.cast_sub (by omega : 1 ≤ r)]
  norm_num

theorem coefficient_pos (i : Fin r) : 0 < coefficient r hr i := by
  by_cases hi : i.val+2 < r
  · simp only [coefficient,CFSGOrthogonalDCartanIntrinsicCoordinates.rationalCoordinates,
      LinearMap.pi_apply,if_pos hi,LinearMap.comp_apply]
    change 0 < (CFSGOrthogonalDCartanIntrinsicCoordinates.prefixSum r i.val
      (integerWeight r):ℚ)
    have hp : 0 < CFSGOrthogonalDCartanIntrinsicCoordinates.prefixSum r i.val
        (integerWeight r) := by
      let zero : Fin r:=⟨0,by omega⟩
      have hz : 0 < integerWeight r zero := by dsimp [integerWeight,zero];omega
      change 0 < ∑ k ∈ Finset.univ.filter (fun k : Fin r=>k.val ≤ i.val),integerWeight r k
      rw [Finset.sum_filter]
      have hle := Finset.single_le_sum
        (f:=fun k : Fin r=>if k.val ≤ i.val then integerWeight r k else 0)
        (fun k _=>by
          change 0 ≤ if k.val ≤ i.val then integerWeight r k else 0
          split_ifs
          · exact weight_nonneg r k
          · rfl)
        (Finset.mem_univ zero)
      have hzero : zero.val ≤ i.val := by dsimp [zero];omega
      change (if zero.val ≤ i.val then integerWeight r zero else 0) ≤
        ∑ k : Fin r,if k.val ≤ i.val then integerWeight r k else 0 at hle
      rw [if_pos hzero] at hle
      exact lt_of_lt_of_le hz hle
    exact_mod_cast hp
  · by_cases hi' : i.val+1 < r
    · simp only [coefficient,CFSGOrthogonalDCartanIntrinsicCoordinates.rationalCoordinates,
        LinearMap.pi_apply,if_neg hi,if_pos hi',LinearMap.sub_apply,
        LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.proj_apply]
      change 0 < (1/2:ℚ)*((∑ k,integerWeight r k:ℤ):ℚ)-
        (integerWeight r ⟨r-1,by omega⟩:ℚ)
      rw [last_zero r hr]
      have hp : (0:ℚ) < ((∑ k,integerWeight r k:ℤ):ℚ) := by
        exact_mod_cast sum_positive r hr
      linarith
    · simp only [coefficient,CFSGOrthogonalDCartanIntrinsicCoordinates.rationalCoordinates,
        LinearMap.pi_apply,if_neg hi,if_neg hi',LinearMap.smul_apply,LinearMap.comp_apply]
      change 0 < (1/2:ℚ)*((∑ k,integerWeight r k:ℤ):ℚ)
      have hp : (0:ℚ) < ((∑ k,integerWeight r k:ℤ):ℚ) := by
        exact_mod_cast sum_positive r hr
      linarith

theorem grading_cartan_sum :
    gradingMatrix r=∑ i : Fin r,coefficient r hr i • cartan ℚ r i := by
  have h:=reconstruction r hr (gradingMatrix r) (grading_mem r)
  have hc : ∀ i,coordinates r hr (gradingMatrix r) (.inl i)=coefficient r hr i := by
    intro i
    have hd : diagonal r (gradingMatrix r)=fun k=>(integerWeight r k:ℚ) := by
      funext k
      simp [diagonal,gradingMatrix,diagonalWeight,integerWeight]
    change CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr
      (diagonal r (gradingMatrix r)) i=coefficient r hr i
    rw [hd,CFSGOrthogonalDRationalCartanCoordinates.coordinates_cast]
    rfl
  have hz : ∀ j : Bool×RootIndex r,coordinates r hr (gradingMatrix r) (.inr j)=0 := by
    rintro ⟨neg,ij | ij⟩
    all_goals
      have hne : ij.val.1≠ij.val.2 := fun h=>ij.property.ne (congrArg Fin.val h)
      cases neg <;> simp [coordinates,CFSGOrthogonalDUniformRootCoordinates.coordinates,
        CFSGOrthogonalDUniformRootCoordinates.entry,gradingMatrix,
        Matrix.diagonal_apply,hne,Ne.symm hne]
  simpa only [Fintype.linearCombination_apply,Fintype.sum_sum_type,hc,hz,
    zero_smul,Finset.sum_const_zero,add_zero,matrix] using h.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanGrading
