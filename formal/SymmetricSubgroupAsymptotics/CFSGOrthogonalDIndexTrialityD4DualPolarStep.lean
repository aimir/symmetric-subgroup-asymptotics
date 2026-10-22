import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PolarHyperplane
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane
import Mathlib.Order.ModularLattice

/-! A genuine quadratic maximal-space step: replace one polar
hyperplane by a singular vector of the target. The intersection with
the target increases, in EVERY characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PolarHyperplane
open CFSGOrthogonalDIndexQuadraticCorrection CFSGOrthogonalDIndexQuadraticNeighborPlane
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem dual_polar_replacement_step (Q : QuadraticForm K V) (P L : Submodule K V)
    (r : ℕ) (hdP : Module.finrank K P = r)
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P)
    (hzP : ∀ x ∈ P, Q x = 0) (hzL : ∀ x ∈ L, Q x = 0)
    (u : V) (huL : u ∈ L) (huP : u ∉ P) :
    ∃ R : Submodule K V, R ≠ P ∧ Module.finrank K R = r ∧
      (∀ x ∈ R, Q x = 0) ∧ Module.finrank K ↥(P ⊓ R) + 1 = r ∧
      Module.finrank K ↥(P ⊓ L) + 1 ≤ Module.finrank K ↥(R ⊓ L) := by
  let H := polarHyperplane Q P u
  let R := H ⊔ Submodule.span K {u}
  have hHP : H ≤ P := inf_le_left
  have huH : u ∉ H := fun h => huP (hHP h)
  have hHrank : Module.finrank K H + 1 = r := (polarHyperplane_finrank Q P hP u huP).trans hdP
  have huR : u ∈ R := Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)
  have hRne : R ≠ P := by
    intro he
    have hh := huR
    rw [he] at hh
    exact huP hh
  have hRrank : Module.finrank K R = r := by
    change Module.finrank K ↥(H ⊔ Submodule.span K {u}) = r
    rw [Submodule.finrank_sup_span_singleton huH]
    exact hHrank
  have hRs : ∀ x ∈ R, Q x = 0 := by
    apply singular_sup Q H (Submodule.span K {u})
    · intro x hx
      exact hzP x (hHP hx)
    · intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp only [Q.map_smul, hzL u huL, smul_zero]
    · intro x hx y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
      have hxu : Q.polarBilin x u = 0 := by
        change QuadraticMap.polar Q x u = 0
        rw [QuadraticMap.polar_comm (Q : V → K) x u]
        exact hx.2
      rw [map_smul, hxu, smul_zero]
  have hdis : (Submodule.span K {u}) ⊓ P = ⊥ :=
    (Submodule.disjoint_span_singleton_of_notMem huP).symm.eq_bot
  have hPR : P ⊓ R = H := by
    rw [inf_comm]
    change (H ⊔ Submodule.span K {u}) ⊓ P = H
    rw [sup_inf_assoc_of_le _ hHP, hdis, sup_bot_eq]
  have hPLH : P ⊓ L ≤ H := by
    intro x hx
    exact ⟨hx.1, polar_zero_of_singular Q L hzL u x huL hx.2⟩
  have hgain : (P ⊓ L) ⊔ Submodule.span K {u} ≤ R ⊓ L :=
    le_inf (sup_le (hPLH.trans le_sup_left) le_sup_right)
      (sup_le inf_le_right ((Submodule.span_singleton_le_iff_mem u L).mpr huL))
  have hdim := Submodule.finrank_mono hgain
  rw [Submodule.finrank_sup_span_singleton (show u ∉ P ⊓ L from fun h => huP h.1)] at hdim
  exact ⟨R, hRne, hRrank, hRs, by rw [hPR]; exact hHrank, hdim⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PolarHyperplane
