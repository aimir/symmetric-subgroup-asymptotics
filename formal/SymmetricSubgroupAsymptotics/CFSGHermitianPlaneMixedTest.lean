import SymmetricSubgroupAsymptotics.CFSGHermitianPlanePairingValues
import Mathlib.Tactic.Abel

/-! A mixed orthogonal test ray detects the relative components of a
point not already on an orthogonal mixed ray. The test is constructed by
two actual pairing values in the opposite plane, uniformly in all fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem exists_hermitian_plane_mixed_test
    (hswap : ∀ v w, hermitianPair sigma H v w = 0 ↔ hermitianPair sigma H w v = 0)
    (P Z : Submodule K (I → K)) (hdP : Module.finrank K P = 2) (hdZ : Module.finrank K Z = 2)
    (hNDz : ∀ z ∈ Z, (∀ x ∈ P, hermitianPair sigma H z x = 0) → z = 0)
    (x y : I → K) (hx : x ∈ P) (hx0 : x ≠ 0) (hyx : hermitianPair sigma H y x ≠ 0) :
    ∃ u ∈ P, ∃ z ∈ Z, u ≠ 0 ∧ z ≠ 0 ∧ hermitianPair sigma H z u = 0 ∧
      hermitianPair sigma H y u ≠ 0 ∧ hermitianPair sigma H x z = -hermitianPair sigma H y u := by
  have hnot : ¬P ≤ K ∙ x := by
    intro hle
    have hh := Submodule.finrank_mono hle
    rw [hdP, finrank_span_singleton hx0] at hh
    omega
  obtain ⟨w, hw, hwnot⟩ := Set.not_subset.mp hnot
  have hu : ∃ u ∈ P, u ∉ K ∙ x ∧ hermitianPair sigma H y u ≠ 0 := by
    by_cases hyw : hermitianPair sigma H y w = 0
    · refine ⟨x + w, P.add_mem hx hw, ?_, ?_⟩
      · intro h
        have hm := (K ∙ x).sub_mem h (Submodule.mem_span_singleton_self x)
        have he : x + w - x = w := by abel
        rw [he] at hm
        exact hwnot hm
      · rw [hermitianPair_add_right, hyw, add_zero]
        exact hyx
    · exact ⟨w, hw, hwnot, hyw⟩
  obtain ⟨u, huP, hunot, hyu⟩ := hu
  have hli : LinearIndependent K ![x,u] :=
    (LinearIndependent.pair_iff' hx0).mpr (fun c he =>
      hunot (he ▸ (K ∙ x).smul_mem c (Submodule.mem_span_singleton_self x)))
  have hle : Submodule.span K (Set.range ![x,u]) ≤ P := by
    apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    fin_cases j
    · exact hx
    · exact huP
  have hdspan : Module.finrank K (Submodule.span K (Set.range ![x,u])) = 2 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hli
  have hspan : Submodule.span K (Set.range ![x,u]) = P :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hdP, hdspan])
  have hND : ∀ z ∈ Z, (∀ v ∈ P, hermitianPair sigma H v z = 0) → z = 0 := by
    intro z hz hzero
    exact hNDz z hz (fun v hv => (hswap v z).mp (hzero v hv))
  obtain ⟨z, hz⟩ := planePairingValues_surjective sigma H Z P hdZ ![x,u] hspan hND
    ![-hermitianPair sigma H y u,0]
  have hzx := congrFun hz (0 : Fin 2)
  have hzu := congrFun hz (1 : Fin 2)
  change hermitianPair sigma H x z.val = -hermitianPair sigma H y u at hzx
  change hermitianPair sigma H u z.val = 0 at hzu
  have hu0 : u ≠ 0 := fun h => hunot (h ▸ (K ∙ x).zero_mem)
  have hz0 : z.val ≠ 0 := by
    intro h
    rw [h, pair_zero_right] at hzx
    exact hyu (neg_eq_zero.mp hzx.symm)
  exact ⟨u, huP, z.val, z.property, hu0, hz0, (hswap u z.val).mp hzu, hyu, hzx⟩

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
