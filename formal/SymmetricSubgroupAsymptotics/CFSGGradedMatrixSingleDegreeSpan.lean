import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport

/-! A homogeneous element of a linear span of operators in distinct
literal degrees belongs to the corresponding single generator line.
This lemma does not claim the same for an arbitrary ambient matrix. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixSingleDegreeSpan
open CFSGGradedMatrixSupport
variable {I J K V : Type*} [CommRing K] [AddCommGroup V] [DecidableEq V]

def degreePart (weight : I→V) (d : V) : Matrix I I K→ₗ[K]Matrix I I K where
  toFun M := Matrix.of (fun i j=>if weight i=weight j+d then M i j else 0)
  map_add' := by intro M N;ext i j;by_cases h : weight i=weight j+d <;> simp [h]
  map_smul' := by intro a M;ext i j;by_cases h : weight i=weight j+d <;> simp [h]

theorem degreePart_eq (weight : I→V) (d : V) (M : Matrix I I K)
    (hM : Supported weight (fun v=>v+d) M) : degreePart weight d M=M := by
  ext i j
  change (if weight i=weight j+d then M i j else 0)=M i j
  by_cases h : weight i=weight j+d
  · exact if_pos h
  · rw [if_neg h,hM i j h]

theorem degreePart_zero_of_other (weight : I→V) (d e : V) (M : Matrix I I K)
    (hM : Supported weight (fun v=>v+e) M) (hde : d≠e) : degreePart weight d M=0 := by
  ext i j
  change (if weight i=weight j+d then M i j else 0)=(0 : Matrix I I K) i j
  by_cases h : weight i=weight j+d
  · have hne : weight i≠weight j+e := by
      intro he
      exact hde (add_left_cancel (h.symm.trans he))
    rw [if_pos h,hM i j hne]
    rfl
  · rw [if_neg h]
    rfl

theorem mem_single_line_of_mem_span (weight : I→V) (d : J→V)
    (hd : Function.Injective d) (X : J→Matrix I I K)
    (hX : ∀j,Supported weight (fun v=>v+d j) (X j))
    (j₀ : J) (M : Matrix I I K) (hM : M∈Submodule.span K (Set.range X))
    (hdeg : Supported weight (fun v=>v+d j₀) M) :
    M∈Submodule.span K ({X j₀} : Set (Matrix I I K)) := by
  have hp : degreePart weight (d j₀) M∈Submodule.span K ({X j₀} : Set (Matrix I I K)) := by
    clear hdeg
    induction hM using Submodule.span_induction with
    | mem N hn=>
      obtain ⟨j,rfl⟩ := hn
      by_cases hj : j=j₀
      · subst j
        rw [degreePart_eq weight (d j₀) (X j₀) (hX j₀)]
        exact Submodule.subset_span (by simp)
      · rw [degreePart_zero_of_other weight (d j₀) (d j) (X j) (hX j)
          (fun h=>hj (hd h).symm)]
        exact Submodule.zero_mem _
    | zero=>rw [map_zero];exact Submodule.zero_mem _
    | add N P _ _ hn hp=>rw [map_add];exact Submodule.add_mem _ hn hp
    | smul a N _ hn=>rw [map_smul];exact Submodule.smul_mem _ a hn
  rw [degreePart_eq weight (d j₀) M hdeg] at hp
  exact hp

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixSingleDegreeSpan
