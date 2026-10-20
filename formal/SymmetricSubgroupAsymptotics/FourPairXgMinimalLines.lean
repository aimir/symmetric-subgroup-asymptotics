import SymmetricSubgroupAsymptotics.FourPairXgCyclicKernelWords
import SymmetricSubgroupAsymptotics.FourPairBinarySocleLines

/-! Two actual invariant Klein lines spanning the literal Xg kernel.
All finite equations are on original eight-point permutations. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace FourPairXgMinimalLines
open FourPairXgCyclicKernelWords

def u (j : Fin 2) : Source :=
  if j = 0 then sourceBasis 0 * sourceBasis 2
  else sourceBasis 0 * sourceBasis 2 * sourceBasis 3

def v (j : Fin 2) : Source := sourceGenerators 4 * u j * (sourceGenerators 4)⁻¹

def elements (j : Fin 2) : Fin 4 → Source := ![1, u j, v j, u j * v j]
def mulIndex (i k : Fin 4) : Fin 4 :=
  (![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]] i) k

private theorem multiplication_checked : ∀ (j : Fin 2) (i k : Fin 4),
    elements j i * elements j k = elements j (mulIndex i k) := by
  decide +kernel
private theorem inverse_checked : ∀ (j : Fin 2) (i : Fin 4),
    (elements j i)⁻¹ = elements j i := by
  decide +kernel

def line (j : Fin 2) : Subgroup Source where
  carrier := Set.range (elements j)
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro x y ⟨i, rfl⟩ ⟨k, rfl⟩
    exact ⟨mulIndex i k, (multiplication_checked j i k).symm⟩
  inv_mem' := by
    rintro x ⟨i, rfl⟩
    exact ⟨i, (inverse_checked j i).symm⟩

theorem line_closure (j : Fin 2) :
    Subgroup.closure (Set.range (elements j)) = line j := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr (fun _ h => h)
  · rintro x ⟨i, rfl⟩
    exact Subgroup.subset_closure (Set.mem_range_self i)

private theorem normalizer_checked : ∀ (j : Fin 2) (g : Fin 6) (i : Fin 4),
    ∃ k : Fin 4, sourceGenerators g * elements j i * (sourceGenerators g)⁻¹ =
      elements j k := by
  decide +kernel

instance line_normal (j : Fin 2) : (line j).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← closureGenerators_full generators]
  have h := generated_le_normalizer_of_generator_conjugates
    (elements j) sourceGenerators (by
      intro g i
      obtain ⟨k, hk⟩ := normalizer_checked j g i
      rw [hk]
      exact Subgroup.subset_closure (Set.mem_range_self k))
  simpa only [line_closure] using h

private theorem cycle_checked : ∀ j : Fin 2,
    u j ≠ 1 ∧
    sourceGenerators 4 * v j * (sourceGenerators 4)⁻¹ = u j * v j ∧
    sourceGenerators 4 * (u j * v j) * (sourceGenerators 4)⁻¹ = u j := by
  decide +kernel

theorem line_minimal (j : Fin 2) : IsMinimalNormalSubgroup (line j) := by
  apply FourPairBinarySocleLines.minimal_of_threeCycle (line j)
    (u j) (v j) (sourceGenerators 4) ⟨1, rfl⟩ ⟨2, rfl⟩ (cycle_checked j).1
  · apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨1, rfl⟩
      · exact (Set.mem_singleton_iff.mp hx) ▸ (show v j ∈ line j from ⟨2, rfl⟩)
    · rintro x ⟨i, rfl⟩
      fin_cases i
      · exact (Subgroup.closure ({u j, v j} : Set Source)).one_mem
      · exact Subgroup.subset_closure (show u j ∈ ({u j, v j} : Set Source) from by simp)
      · exact Subgroup.subset_closure (show v j ∈ ({u j, v j} : Set Source) from by simp)
      · exact (Subgroup.closure ({u j, v j} : Set Source)).mul_mem
          (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · rintro x ⟨i, rfl⟩
    fin_cases i <;> simp [elements]
  · rfl
  · exact (cycle_checked j).2.1
  · exact (cycle_checked j).2.2


private theorem basis_checked : ∀ i : Fin 4,
    sourceBasis i = (![u 0 * v 0 * v 1, v 0 * u 1, v 0 * v 1, u 0 * u 1] i) := by
  decide +kernel

theorem lines_span_kernel : line 0 ⊔ line 1 = kernel := by
  have hline : ∀ j : Fin 2, line j ≤ kernel := by
    intro j
    have hu : u j ∈ kernel := by
      have hb : ∀ i, sourceBasis i ∈ kernel :=
        fun i => Subgroup.subset_closure (Set.mem_range_self i)
      by_cases hj : j = 0
      · simp only [u, hj, if_pos rfl]
        exact kernel.mul_mem (hb 0) (hb 2)
      · simp only [u, hj, if_false]
        exact kernel.mul_mem (kernel.mul_mem (hb 0) (hb 2)) (hb 3)
    have hv : v j ∈ kernel :=
      (inferInstance : kernel.Normal).conj_mem (u j) hu (sourceGenerators 4)
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact kernel.one_mem
    · exact hu
    · exact hv
    · exact kernel.mul_mem hu hv
  apply le_antisymm (sup_le (hline 0) (hline 1))
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i, rfl⟩
  have hu0 : u 0 ∈ line 0 ⊔ line 1 := (show line 0 ≤ line 0 ⊔ line 1 from le_sup_left) (show u 0 ∈ line 0 from ⟨1, rfl⟩)
  have hv0 : v 0 ∈ line 0 ⊔ line 1 := (show line 0 ≤ line 0 ⊔ line 1 from le_sup_left) (show v 0 ∈ line 0 from ⟨2, rfl⟩)
  have hu1 : u 1 ∈ line 0 ⊔ line 1 := (show line 1 ≤ line 0 ⊔ line 1 from le_sup_right) (show u 1 ∈ line 1 from ⟨1, rfl⟩)
  have hv1 : v 1 ∈ line 0 ⊔ line 1 := (show line 1 ≤ line 0 ⊔ line 1 from le_sup_right) (show v 1 ∈ line 1 from ⟨2, rfl⟩)
  rw [basis_checked i]
  fin_cases i
  · exact (line 0 ⊔ line 1).mul_mem ((line 0 ⊔ line 1).mul_mem hu0 hv0) hv1
  · exact (line 0 ⊔ line 1).mul_mem hv0 hu1
  · exact (line 0 ⊔ line 1).mul_mem hv0 hv1
  · exact (line 0 ⊔ line 1).mul_mem hu0 hu1

/-- The whole actual binary kernel lies in the original group socle. -/
theorem kernel_le_socle : kernel ≤ finiteGroupSocle Source := by
  rw [← lines_span_kernel]
  apply sup_le
  · intro x hx
    exact Subgroup.subset_normalClosure ⟨line 0, line_minimal 0, hx⟩
  · intro x hx
    exact Subgroup.subset_normalClosure ⟨line 1, line_minimal 1, hx⟩

end FourPairXgMinimalLines
end SymmetricSubgroupAsymptotics
