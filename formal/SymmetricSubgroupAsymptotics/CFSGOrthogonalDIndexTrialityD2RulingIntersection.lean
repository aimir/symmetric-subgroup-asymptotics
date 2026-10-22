import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2RulingPlanes
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FieldSimp

/-! Two opposite residual ruling planes meet in exactly the actual
outer-product line. In particular the two plane families are disjoint;
this is a proved distinction, not a two-valued label assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

theorem exists_factor_coordinate (u : Fin 2 → K) (hu : u ≠ 0) : ∃ i, u i ≠ 0 := by
  by_contra hn
  simp only [not_exists, not_not] at hn
  exact hu (funext hn)

theorem outer_nonzero (u v : Fin 2 → K) (hu : u ≠ 0) (hv : v ≠ 0) :
    columnMap K u v ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_factor_coordinate K u hu
  obtain ⟨j, hj⟩ := exists_factor_coordinate K v hv
  intro he
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A i j) he
  change u i * v j = 0 at hh
  exact mul_ne_zero hi hj hh

theorem column_inf_row_eq_span (u v : Fin 2 → K) (hu : u ≠ 0) :
    columnPlane K u ⊓ rowPlane K v = Submodule.span K {columnMap K u v} := by
  obtain ⟨i, hi⟩ := exists_factor_coordinate K u hu
  apply le_antisymm
  · intro A hA
    obtain ⟨p, hp⟩ := hA.1
    obtain ⟨q, hq⟩ := hA.2
    have he : columnMap K u p = rowMap K v q := hp.trans hq.symm
    let a := q i / u i
    have hpexpr : p = a • v := by
      funext j
      have hh := congrArg (fun B : Matrix (Fin 2) (Fin 2) K => B i j) he
      change u i * p j = q i * v j at hh
      change p j = (q i / u i) * v j
      calc
        p j = (u i * p j) / u i := by field_simp [hi] <;> ring
        _ = (q i * v j) / u i := congrArg (fun x => x / u i) hh
        _ = (q i / u i) * v j := by ring
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    calc
      a • columnMap K u v = columnMap K u p := by
        rw [hpexpr]
        ext j k
        change a * (u j * v k) = u j * (a * v k)
        ring
      _ = A := hp
  · apply Submodule.span_le.mpr
    rintro A rfl
    exact ⟨⟨v, rfl⟩, ⟨u, rfl⟩⟩

theorem column_inf_row_finrank (u v : Fin 2 → K) (hu : u ≠ 0) (hv : v ≠ 0) :
    Module.finrank K ↥(columnPlane K u ⊓ rowPlane K v) = 1 := by
  rw [column_inf_row_eq_span K u v hu]
  exact finrank_span_singleton (outer_nonzero K u v hu hv)

theorem columnPlane_ne_rowPlane (u v : Fin 2 → K) (hu : u ≠ 0) (hv : v ≠ 0) :
    columnPlane K u ≠ rowPlane K v := by
  intro he
  have hh := column_inf_row_finrank K u v hu hv
  rw [he, inf_idem, rowPlane_finrank K v hv] at hh
  omega

theorem originalColumnPlane_ne_originalRowPlane (u v : Fin 2 → K)
    (hu : u ≠ 0) (hv : v ≠ 0) : originalColumnPlane K u ≠ originalRowPlane K v := by
  intro he
  exact columnPlane_ne_rowPlane K u v hu hv
    ((Submodule.map_injective_of_injective (determinantCoordinates K).symm.injective) he)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
