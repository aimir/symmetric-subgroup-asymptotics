import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2RulingPlanes
import Mathlib.LinearAlgebra.Span.Basic

/-! The residual ruling plane remembers exactly its original factor
line. Thus its projective parameter has no unproved identification or
extra scalar ambiguity. The inclusion statement also covers zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

theorem columnPlane_le_iff_factor_line_le (u v : Fin 2 → K) :
    columnPlane K u ≤ columnPlane K v ↔ Submodule.span K {u} ≤ Submodule.span K {v} := by
  constructor
  · intro h
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    have hm : columnMap K u (Pi.single (0 : Fin 2) 1) ∈ columnPlane K u := ⟨_, rfl⟩
    obtain ⟨p, hp⟩ := h hm
    apply Submodule.mem_span_singleton.mpr
    refine ⟨p 0, ?_⟩
    funext i
    have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A i 0) hp
    change v i * p 0 = u i * 1 at hh
    simpa only [Pi.smul_apply, smul_eq_mul, mul_one, mul_comm] using hh
  · intro h A hA
    have hm : u ∈ Submodule.span K {v} := h (Submodule.mem_span_singleton_self _)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    obtain ⟨p, rfl⟩ := hA
    refine ⟨a • p, ?_⟩
    rw [← ha]
    ext i j
    change v i * (a * p j) = (a * v i) * p j
    ring

theorem rowPlane_le_iff_factor_line_le (u v : Fin 2 → K) :
    rowPlane K u ≤ rowPlane K v ↔ Submodule.span K {u} ≤ Submodule.span K {v} := by
  constructor
  · intro h
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    have hm : rowMap K u (Pi.single (0 : Fin 2) 1) ∈ rowPlane K u := ⟨_, rfl⟩
    obtain ⟨p, hp⟩ := h hm
    apply Submodule.mem_span_singleton.mpr
    refine ⟨p 0, ?_⟩
    funext j
    have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 j) hp
    change p 0 * v j = 1 * u j at hh
    simpa only [Pi.smul_apply, smul_eq_mul, one_mul] using hh
  · intro h A hA
    have hm : u ∈ Submodule.span K {v} := h (Submodule.mem_span_singleton_self _)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    obtain ⟨p, rfl⟩ := hA
    refine ⟨a • p, ?_⟩
    rw [← ha]
    ext i j
    change (a * p i) * v j = p i * (a * v j)
    ring

theorem columnPlane_eq_iff_factor_line_eq (u v : Fin 2 → K) :
    columnPlane K u = columnPlane K v ↔ Submodule.span K {u} = Submodule.span K {v} := by
  constructor
  · intro h
    exact le_antisymm ((columnPlane_le_iff_factor_line_le K u v).mp h.le)
      ((columnPlane_le_iff_factor_line_le K v u).mp h.ge)
  · intro h
    exact le_antisymm ((columnPlane_le_iff_factor_line_le K u v).mpr h.le)
      ((columnPlane_le_iff_factor_line_le K v u).mpr h.ge)

theorem rowPlane_eq_iff_factor_line_eq (u v : Fin 2 → K) :
    rowPlane K u = rowPlane K v ↔ Submodule.span K {u} = Submodule.span K {v} := by
  constructor
  · intro h
    exact le_antisymm ((rowPlane_le_iff_factor_line_le K u v).mp h.le)
      ((rowPlane_le_iff_factor_line_le K v u).mp h.ge)
  · intro h
    exact le_antisymm ((rowPlane_le_iff_factor_line_le K u v).mpr h.le)
      ((rowPlane_le_iff_factor_line_le K v u).mpr h.ge)

theorem originalColumnPlane_eq_iff_factor_line_eq (u v : Fin 2 → K) :
    originalColumnPlane K u = originalColumnPlane K v ↔ Submodule.span K {u} = Submodule.span K {v} := by
  constructor
  · intro h
    apply (columnPlane_eq_iff_factor_line_eq K u v).mp
    exact (Submodule.map_injective_of_injective (determinantCoordinates K).symm.injective) h
  · intro h
    exact congrArg (fun P => P.map (determinantCoordinates K).symm.toLinearMap)
      ((columnPlane_eq_iff_factor_line_eq K u v).mpr h)

theorem originalRowPlane_eq_iff_factor_line_eq (u v : Fin 2 → K) :
    originalRowPlane K u = originalRowPlane K v ↔ Submodule.span K {u} = Submodule.span K {v} := by
  constructor
  · intro h
    apply (rowPlane_eq_iff_factor_line_eq K u v).mp
    exact (Submodule.map_injective_of_injective (determinantCoordinates K).symm.injective) h
  · intro h
    exact congrArg (fun P => P.map (determinantCoordinates K).symm.toLinearMap)
      ((rowPlane_eq_iff_factor_line_eq K u v).mpr h)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
