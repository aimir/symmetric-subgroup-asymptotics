import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Lean.Elab.Tactic.Omega

/-! Disjoint singular two-planes in a nondegenerate space of dimension
at most seven cannot be mutually orthogonal. Their cross-orthogonal
axes therefore have dimension at most one. No polar census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarRankThreeAxisBound
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem cross_axis_finrank_le_one (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (hV : Module.finrank K V ≤ 7)
    (P Q : Submodule K V) (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2)
    (hd : Disjoint P Q) (zP : ∀ x ∈ P, ∀ y ∈ P, B x y = 0)
    (zQ : ∀ x ∈ Q, ∀ y ∈ Q, B x y = 0) :
    Module.finrank K (P ⊓ B.orthogonal Q : Submodule K V) ≤ 1 := by
  let A : Submodule K V := P ⊓ B.orthogonal Q
  by_contra hn
  change ¬Module.finrank K A ≤ 1 at hn
  have hlarge : 2 ≤ Module.finrank K A := by omega
  have he : A = P := Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hP]; exact hlarge)
  have hPo : P ≤ B.orthogonal Q := he.ge.trans inf_le_right
  have hc (p : V) (hp : p ∈ P) (q : V) (hq : q ∈ Q) : B p q = 0 :=
    (hs p q).trans (hPo hp q hq)
  let S : Submodule K V := P ⊔ Q
  have hz : ∀ x ∈ S, ∀ y ∈ S, B x y = 0 := by
    intro x hx y hy
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨p', hp', q', hq', rfl⟩ := Submodule.mem_sup.mp hy
    have hrev : B q p' = 0 := hPo hp' q hq
    simp only [map_add, LinearMap.add_apply, zP p hp p' hp', hc p hp q' hq', hrev,
      zQ q hq q' hq', add_zero]
  have hSo : S ≤ B.orthogonal S := by
    intro x hx y hy
    exact hz y hy x hx
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [hd.eq_bot, finrank_bot, hP, hQ, add_zero] at hdim
  change Module.finrank K S = 2 + 2 at hdim
  have hSd : Module.finrank K S = 4 := by omega
  have hle := Submodule.finrank_mono hSo
  have hsum := B.finrank_add_finrank_orthogonal' S
  rw [hB.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero] at hsum
  change Module.finrank K S + Module.finrank K (B.orthogonal S) = Module.finrank K V at hsum
  omega

end SymmetricSubgroupAsymptotics.CFSGPolarRankThreeAxisBound
