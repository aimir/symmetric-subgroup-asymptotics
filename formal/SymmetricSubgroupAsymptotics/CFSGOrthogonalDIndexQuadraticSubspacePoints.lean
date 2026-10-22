import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Literal Q-singular points, planes and subspaces. The predicate is
quadratic zero throughout, including characteristic two; it is never
replaced by polar self-orthogonality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

abbrev Points (Q : QuadraticForm K V) :=
  {P : Submodule K V // Module.finrank K P = 1 ∧ ∀ x ∈ P, Q x = 0}
abbrev Planes (Q : QuadraticForm K V) :=
  {P : Submodule K V // Module.finrank K P = 2 ∧ ∀ x ∈ P, Q x = 0}
abbrev Subspaces (Q : QuadraticForm K V) := {W : Submodule K V // ∀ x ∈ W, Q x = 0}

def ray (Q : QuadraticForm K V) (v : V) (hv : v ≠ 0) (hz : Q v = 0) : Points Q :=
  ⟨Submodule.span K {v}, finrank_span_singleton hv, by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [Q.map_smul, hz, smul_zero]⟩

theorem point_span (Q : QuadraticForm K V) (P : Points Q)
    (v : V) (hvP : v ∈ P.val) (hv : v ≠ 0) : Submodule.span K {v} = P.val :=
  Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hvP)
    (by rw [P.property.1, finrank_span_singleton hv])

theorem point_eq_of_common_nonzero (Q : QuadraticForm K V) (P R : Points Q)
    (v : V) (hp : v ∈ P.val) (hr : v ∈ R.val) (hv : v ≠ 0) : P = R :=
  Subtype.ext ((point_span Q P v hp hv).symm.trans (point_span Q R v hr hv))

theorem point_nonzero (Q : QuadraticForm K V) (P : Points Q) : ∃ v ∈ P.val, v ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  exact Submodule.one_le_finrank_iff.mp (by rw [P.property.1])

def joinPlane (Q : QuadraticForm K V) (W : Subspaces Q) (P R : Points Q)
    (hP : P.val ≤ W.val) (hR : R.val ≤ W.val) (hne : P ≠ R) : Planes Q := by
  have hbot : (P.val ⊓ R.val : Submodule K V) = ⊥ := by
    by_contra hn
    have hlo : 1 ≤ Module.finrank K ↥(P.val ⊓ R.val) := Submodule.one_le_finrank_iff.mpr hn
    have hp : P.val ⊓ R.val = P.val := Submodule.eq_of_le_of_finrank_le inf_le_left
      (by rw [P.property.1]; exact hlo)
    have hr : P.val ⊓ R.val = R.val := Submodule.eq_of_le_of_finrank_le inf_le_right
      (by rw [R.property.1]; exact hlo)
    exact hne (Subtype.ext (hp.symm.trans hr))
  have hd := Submodule.finrank_sup_add_finrank_inf_eq P.val R.val
  rw [hbot, finrank_bot, P.property.1, R.property.1, add_zero] at hd
  exact ⟨P.val ⊔ R.val, hd, fun x hx => W.property x ((sup_le hP hR) hx)⟩

theorem subspace_ext (Q : QuadraticForm K V) {W Z : Subspaces Q}
    (h : ∀ P : Points Q, P.val ≤ W.val ↔ P.val ≤ Z.val) : W = Z := by
  have hle : ∀ A C : Subspaces Q,
      (∀ P : Points Q, P.val ≤ A.val → P.val ≤ C.val) → A.val ≤ C.val := by
    intro A C hac v hv
    by_cases hz : v = 0
    · exact hz ▸ C.val.zero_mem
    let P := ray Q v hz (A.property v hv)
    have hp : P.val ≤ A.val := (Submodule.span_singleton_le_iff_mem _ _).mpr hv
    exact hac P hp (Submodule.subset_span (by simp))
  exact Subtype.ext (le_antisymm (hle W Z (fun P => (h P).mp)) (hle Z W (fun P => (h P).mpr)))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
