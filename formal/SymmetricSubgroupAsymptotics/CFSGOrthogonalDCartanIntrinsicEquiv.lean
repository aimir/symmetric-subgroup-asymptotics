import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanIntrinsicCoordinates

/-! The literal integral D Cartan columns are a Z-basis of the genuine
even-sum diagonal lattice. The inverse is defined only on that intrinsic
codomain, so no impossible ambient integer splitting is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanIntrinsicEquiv
open CFSGOrthogonalDCartanParityLattice CFSGOrthogonalDCartanParitySpan
open CFSGOrthogonalDCartanIntrinsicCoordinates
variable (r : ℕ)

def columns (hr : 4 ≤ r) : (Fin r→ℤ)→ₗ[ℤ](evenSum r) :=
  (Fintype.linearCombination ℤ (column r)).codRestrict (evenSum r)
    (combination_mem r hr)

theorem rationalCoordinates_combination (hr : 4 ≤ r) (a : Fin r→ℤ) :
    rationalCoordinates r hr (Fintype.linearCombination ℤ (column r) a)=
      fun j=>(a j:ℚ) := by
  rw [Fintype.linearCombination_apply]
  simp only [map_sum,map_smul,rationalCoordinates_column]
  funext j
  simp [Finset.sum_apply,Pi.single_apply,←Int.cast_smul_eq_zsmul ℚ]

theorem columns_injective (hr : 4 ≤ r) : Function.Injective (columns r hr) := by
  intro a b hab
  have h:=congrArg (rationalCoordinates r hr) (congrArg Subtype.val hab)
  change rationalCoordinates r hr (Fintype.linearCombination ℤ (column r) a)=
    rationalCoordinates r hr (Fintype.linearCombination ℤ (column r) b) at h
  rw [rationalCoordinates_combination,rationalCoordinates_combination] at h
  funext j
  exact Int.cast_injective (congrFun h j)

theorem columns_surjective (hr : 4 ≤ r) : Function.Surjective (columns r hr) := by
  intro x
  have hx : x.val∈Submodule.span ℤ (Set.range (column r)) := by
    rw [span_columns_eq_evenSum r hr]
    exact x.property
  obtain ⟨a,ha⟩:=(Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  refine ⟨a,Subtype.ext ?_⟩
  change Fintype.linearCombination ℤ (column r) a=x.val
  simpa only [Fintype.linearCombination_apply] using ha

def equiv (hr : 4 ≤ r) : (Fin r→ℤ)≃ₗ[ℤ](evenSum r) :=
  LinearEquiv.ofBijective (columns r hr) ⟨columns_injective r hr,columns_surjective r hr⟩

def coordinates (hr : 4 ≤ r) : (evenSum r)→ₗ[ℤ](Fin r→ℤ) :=
  (equiv r hr).symm.toLinearMap

theorem coordinates_column (hr : 4 ≤ r) (j : Fin r) :
    coordinates r hr ⟨column r j,column_mem r hr j⟩=Pi.single j 1 := by
  have he : columns r hr (Pi.single j 1)=⟨column r j,column_mem r hr j⟩ := by
    apply Subtype.ext
    change Fintype.linearCombination ℤ (column r) (Pi.single j 1)=column r j
    rw [Fintype.linearCombination_apply_single]
    exact (Int.cast_smul_eq_zsmul ℤ (1:ℤ) (column r j)).trans (one_zsmul (column r j))
  rw [←he]
  exact (equiv r hr).symm_apply_apply (Pi.single j 1)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanIntrinsicEquiv
