import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2FactorLines
import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionFamilies

/-! Complete exhaustion of original residual maximal singular planes
by the two actual ruling families. A determinant-zero submodule has
one uniform column line or one uniform row line; dimension two then
forces equality with the corresponding literal ruling plane. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

theorem determinant_zero_plane_ruling (P : Submodule K (Matrix (Fin 2) (Fin 2) K))
    (hP : Module.finrank K P = 2) (hdet : ∀ A ∈ P, Matrix.det A = 0) :
    (∃ u : Fin 2 → K, u ≠ 0 ∧ P = columnPlane K u) ∨
      (∃ v : Fin 2 → K, v ≠ 0 ∧ P = rowPlane K v) := by
  classical
  let I := {A : Matrix (Fin 2) (Fin 2) K // A ∈ P ∧ A ≠ 0}
  have hfactor : ∀ i : I, ∃ u p : Fin 2 → K,
      u ≠ 0 ∧ p ≠ 0 ∧ i.val = columnMap K u p := by
    intro i
    exact exists_nonzero_outer_factors K i.val i.property.2 (hdet i.val i.property.1)
  choose u p hu hp hfac using hfactor
  have hpair : ∀ i j : I, Submodule.span K {u i} = Submodule.span K {u j} ∨
      Submodule.span K {p i} = Submodule.span K {p j} := by
    intro i j
    apply pairwise_factor_line_alternative K (u i) (p i) (u j) (p j) (hu i) (hp i) (hu j) (hp j)
    have hh := hdet (i.val + j.val) (P.add_mem i.property.1 j.property.1)
    rwa [hfac i, hfac j] at hh
  have huniform := CFSGTypeATransvectionFamilies.uniform_coordinate_of_pairwise
    (fun i : I => Submodule.span K {u i}) (fun i : I => Submodule.span K {p i}) hpair
  have hne : P ≠ ⊥ := by
    intro he
    have hh := congrArg (fun W : Submodule K (Matrix (Fin 2) (Fin 2) K) => Module.finrank K W) he
    change Module.finrank K P = Module.finrank K (⊥ : Submodule K (Matrix (Fin 2) (Fin 2) K)) at hh
    rw [hP, finrank_bot] at hh
    omega
  obtain ⟨A0, hA0, hnA0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let i0 : I := ⟨A0, hA0, hnA0⟩
  rcases huniform with hc | hr
  · left
    refine ⟨u i0, hu i0, ?_⟩
    have hle : P ≤ columnPlane K (u i0) := by
      intro A hA
      by_cases hz : A = 0
      · exact hz ▸ (columnPlane K (u i0)).zero_mem
      let i : I := ⟨A, hA, hz⟩
      have hmem : u i ∈ Submodule.span K {u i0} := by
        have hci : Submodule.span K {u i} = Submodule.span K {u i0} := hc i i0
        rw [← hci]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
      refine ⟨a • p i, ?_⟩
      calc
        columnMap K (u i0) (a • p i) = columnMap K (u i) (p i) := by
          rw [← ha]
          ext j k
          change u i0 j * (a * p i k) = (a * u i0 j) * p i k
          ring
        _ = A := (hfac i).symm
    exact Submodule.eq_of_le_of_finrank_le hle (by rw [columnPlane_finrank K _ (hu i0), hP])
  · right
    refine ⟨p i0, hp i0, ?_⟩
    have hle : P ≤ rowPlane K (p i0) := by
      intro A hA
      by_cases hz : A = 0
      · exact hz ▸ (rowPlane K (p i0)).zero_mem
      let i : I := ⟨A, hA, hz⟩
      have hmem : p i ∈ Submodule.span K {p i0} := by
        have hri : Submodule.span K {p i} = Submodule.span K {p i0} := hr i i0
        rw [← hri]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
      refine ⟨a • u i, ?_⟩
      calc
        rowMap K (p i0) (a • u i) = columnMap K (u i) (p i) := by
          rw [← ha]
          ext j k
          change (a * u i j) * p i0 k = u i j * (a * p i0 k)
          ring
        _ = A := (hfac i).symm
    exact Submodule.eq_of_le_of_finrank_le hle (by rw [rowPlane_finrank K _ (hp i0), hP])

theorem original_singular_plane_ruling (P : Submodule K (Index 2 → K))
    (hP : Module.finrank K P = 2) (hPs : ∀ x ∈ P, splitQuadraticForm K 2 x = 0) :
    (∃ u : Fin 2 → K, u ≠ 0 ∧ P = originalColumnPlane K u) ∨
      (∃ v : Fin 2 → K, v ≠ 0 ∧ P = originalRowPlane K v) := by
  let e := determinantCoordinates K
  let R := P.map e.toLinearMap
  have hd : Module.finrank K R = 2 := (e.finrank_map_eq P).trans hP
  have hz : ∀ A ∈ R, Matrix.det A = 0 := by
    rintro A ⟨x, hx, rfl⟩
    exact (determinantCoordinates_det K x).trans (hPs x hx)
  have hback : R.map e.symm.toLinearMap = P := by
    rw [← Submodule.map_comp]
    have hh : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.symm_apply_apply x
    rw [hh, Submodule.map_id]
  rcases determinant_zero_plane_ruling K R hd hz with ⟨u, hu, he⟩ | ⟨v, hv, he⟩
  · exact Or.inl ⟨u, hu, hback.symm.trans (congrArg (fun S => S.map e.symm.toLinearMap) he)⟩
  · exact Or.inr ⟨v, hv, hback.symm.trans (congrArg (fun S => S.map e.symm.toLinearMap) he)⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
