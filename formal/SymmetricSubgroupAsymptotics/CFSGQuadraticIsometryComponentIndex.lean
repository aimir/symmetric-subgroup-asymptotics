import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularComponents
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Lean.Elab.Tactic.Omega

/-! Genuine maximal-singular parity gives at most two components in
the ACTUAL quadratic isometry group. The index bound follows from the
proved triple parity, with no orthogonal-group classification or
characteristic restriction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticIsometryComponentIndex
open CFSGOrthogonalDIndexSingularComponents CFSGOrthogonalDIndexSingularParity
open CFSGOrthogonalDIndexSingularTransport

private theorem even_third_of_even_sum_of_not_even (a b c : ℕ)
    (ht : Even (a + b + c)) (ha : ¬ Even a) (hb : ¬ Even b) : Even c := by
  simp only [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at ht ha hb ⊢
  omega

theorem subgroup_index_dvd_two_of_outside_mul {G : Type*} [Group G] (H : Subgroup G)
    (hmul : ∀ a b : G, a ∉ H → b ∉ H → a * b ∈ H) : H.index ∣ 2 := by
  classical
  apply H.index_dvd_two_iff.mpr
  by_cases htop : H = ⊤
  · exact ⟨1, fun b => Or.inr (by rw [htop]; trivial)⟩
  · have hex : ∃ a : G, a ∉ H := by
      by_contra hh
      apply htop
      apply top_unique
      intro a _
      by_contra ha
      exact hh ⟨a, ha⟩
    obtain ⟨a, ha⟩ := hex
    refine ⟨a, fun b => ?_⟩
    by_cases hb : b ∈ H
    · exact Or.inr hb
    · exact Or.inl (hmul b a hb ha)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem component_mul_mem_of_not_mem (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (r : ℕ) (hV : Module.finrank K V = 2 * r)
    (P : Submodule K V) (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P)
    (hzP : ∀ x : P, Q (x : V) = 0)
    (f g : isometryGroup Q)
    (hf : f ∉ componentStabilizer Q hQ r hV P hP hzP)
    (hg : g ∉ componentStabilizer Q hQ r hV P hP hzP) :
    f * g ∈ componentStabilizer Q hQ r hV P hP hzP := by
  let Pf := P.map f.val.toLinearMap
  let Pg := P.map g.val.toLinearMap
  let Pfg := P.map (f.val * g.val).toLinearMap
  have hfg : Pg.map f.val.toLinearMap = Pfg := by
    rw [← Submodule.map_comp]
    rfl
  have hd : distance r Pf Pfg = distance r P Pg := by
    change r - Module.finrank K (Pf ⊓ Pfg : Submodule K V) =
      r - Module.finrank K (P ⊓ Pg : Submodule K V)
    rw [← hfg]
    exact congrArg (fun a : ℕ => r - a) (intersection_map_finrank f.val P Pg)
  have hPf := map_self_orthogonal Q f.val f.property P hP
  have hPfg := map_self_orthogonal Q (f.val * g.val) (f * g).property P hP
  have hzPf := map_singular Q f.val f.property P hzP
  have hzPfg := map_singular Q (f.val * g.val) (f * g).property P hzP
  change ¬ Even (distance r P Pf) at hf
  change ¬ Even (distance r P Pg) at hg
  change Even (distance r P Pfg)
  apply even_third_of_even_sum_of_not_even (distance r P Pf) (distance r Pf Pfg)
    (distance r P Pfg)
    (even_three_distances Q hQ r hV P Pf Pfg hP hPf hPfg hzP hzPf hzPfg) hf
  rw [hd]
  exact hg

theorem componentStabilizer_index_dvd_two (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (r : ℕ) (hV : Module.finrank K V = 2 * r)
    (P : Submodule K V) (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P)
    (hzP : ∀ x : P, Q (x : V) = 0) :
    (componentStabilizer Q hQ r hV P hP hzP).index ∣ 2 :=
  subgroup_index_dvd_two_of_outside_mul _
    (component_mul_mem_of_not_mem Q hQ r hV P hP hzP)

theorem componentStabilizer_index_le_two (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (r : ℕ) (hV : Module.finrank K V = 2 * r)
    (P : Submodule K V) (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P)
    (hzP : ∀ x : P, Q (x : V) = 0) :
    (componentStabilizer Q hQ r hV P hP hzP).index ≤ 2 :=
  Nat.le_of_dvd (by decide : 0 < 2) (componentStabilizer_index_dvd_two Q hQ r hV P hP hzP)

end SymmetricSubgroupAsymptotics.CFSGQuadraticIsometryComponentIndex
