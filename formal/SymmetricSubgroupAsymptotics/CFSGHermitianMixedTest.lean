import SymmetricSubgroupAsymptotics.CFSGHermitianIndependentPairingValues
import Mathlib.Tactic.Abel

/-! A separating orthogonal mixed ray exists at every opposed rank
at least two. Independent cross-pairing prescription replaces a
rank-two dimension count. No hypothesis on the opposite dimension is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem exists_hermitian_mixed_test
    (hswap : ∀ v w, hermitianPair sigma H v w = 0 ↔ hermitianPair sigma H w v = 0)
    (P Z : Submodule K (I → K)) (hdP : 2 ≤ Module.finrank K P)
    (hNDp : ∀ x ∈ P, (∀ z ∈ Z, hermitianPair sigma H x z = 0) → x = 0)
    (x y : I → K) (hx : x ∈ P) (hx0 : x ≠ 0) (hyx : hermitianPair sigma H y x ≠ 0) :
    ∃ u ∈ P, ∃ z ∈ Z, u ≠ 0 ∧ z ≠ 0 ∧ hermitianPair sigma H z u = 0 ∧
      hermitianPair sigma H y u ≠ 0 ∧ hermitianPair sigma H x z = -hermitianPair sigma H y u := by
  have hnot : ¬P ≤ K ∙ x := by
    intro hle
    have hh := Submodule.finrank_mono hle
    rw [finrank_span_singleton hx0] at hh
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
  obtain ⟨z,hzZ,hzx,hzu⟩ := independent_hermitian_pair_values sigma H P Z hNDp x u hx huP hli
    (-hermitianPair sigma H y u) 0
  change hermitianPair sigma H x z = -hermitianPair sigma H y u at hzx
  change hermitianPair sigma H u z = 0 at hzu
  have hu0 : u ≠ 0 := fun h => hunot (h ▸ (K ∙ x).zero_mem)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, pair_zero_right] at hzx
    exact hyu (neg_eq_zero.mp hzx.symm)
  exact ⟨u, huP, z, hzZ, hu0, hz0, (hswap u z).mp hzu, hyu, hzx⟩

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
