import SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionPartition
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases

/-! A transverse singular vector orthogonal to a singular two-plane
produces an adjacent plane through the SAME point. Plane equality keeps
the exact proportional-vector fibre, via an actual linear left inverse. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarCommonPointPlanes
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]

def pairPlane (u z : V) : Submodule K V := Submodule.span K {u, z}

theorem pairPlane_finrank (u z : V) (hu : u ≠ 0) (hz : ∀ a : K, z ≠ a • u) :
    Module.finrank K (pairPlane (K := K) u z) = 2 := by
  have hi : LinearIndependent K ![u, z] :=
    (LinearIndependent.pair_iff' hu).mpr (fun a he => hz a he.symm)
  have hr : Set.range ![u, z] = ({u, z} : Set V) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (hx | hx)
      · exact ⟨0, hx.symm⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp hx).symm⟩
  have hd := finrank_span_eq_card hi
  rw [hr, Fintype.card_fin] at hd
  exact hd

omit [FiniteDimensional K V] in
theorem pairPlane_singular (B : LinearMap.BilinForm K V) (u z : V)
    (hu : B u u = 0) (hz : B z z = 0) (huz : B u z = 0) (hzu : B z u = 0) :
    ∀ x ∈ pairPlane (K := K) u z, ∀ y ∈ pairPlane (K := K) u z, B x y = 0 := by
  intro x hx y hy
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hu, hz, huz, hzu, smul_zero, add_zero]

omit [FiniteDimensional K V] in
theorem singular_sup (B : LinearMap.BilinForm K V) (hs : ∀ x y, B x y = B y x)
    (P R : Submodule K V) (hP : ∀ x ∈ P, ∀ y ∈ P, B x y = 0)
    (hR : ∀ x ∈ R, ∀ y ∈ R, B x y = 0)
    (hc : ∀ x ∈ P, ∀ y ∈ R, B x y = 0) :
    ∀ x ∈ P ⊔ R, ∀ y ∈ P ⊔ R, B x y = 0 := by
  intro x hx y hy
  obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨p', hp', r', hr', rfl⟩ := Submodule.mem_sup.mp hy
  have hrev : B r p' = 0 := (hs r p').trans (hc p' hp' r hr)
  simp only [map_add, LinearMap.add_apply, hP p hp p' hp', hc p hp r' hr',
    hrev, hR r hr r' hr', add_zero]

theorem pairPlane_adjacent_data (B : LinearMap.BilinForm K V) (hs : ∀ x y, B x y = B y x)
    (P : Submodule K V) (hP : Module.finrank K P = 2)
    (hPs : ∀ x ∈ P, ∀ y ∈ P, B x y = 0)
    (u z : V) (huP : u ∈ P) (hu : u ≠ 0) (hz : B z z = 0) (hzP : z ∉ P)
    (hPz : ∀ x ∈ P, B x z = 0) :
    P ≠ pairPlane (K := K) u z ∧ Module.finrank K (P ⊓ pairPlane (K := K) u z : Submodule K V) = 1 ∧
      (∀ x ∈ P ⊔ pairPlane (K := K) u z, ∀ y ∈ P ⊔ pairPlane (K := K) u z, B x y = 0) := by
  have huR : u ∈ pairPlane (K := K) u z := Submodule.subset_span (Or.inl rfl)
  have hzR : z ∈ pairPlane (K := K) u z := Submodule.subset_span (Or.inr rfl)
  have hne : P ≠ pairPlane (K := K) u z := fun he => hzP (he.symm ▸ hzR)
  have hnot (a : K) : z ≠ a • u := by
    intro he
    apply hzP
    rw [he]
    exact P.smul_mem a huP
  have hd := pairPlane_finrank u z hu hnot
  have hin : Submodule.span K {u} ≤ P ⊓ pairPlane (K := K) u z := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨huP, huR⟩
  have hlo := Submodule.finrank_mono hin
  rw [finrank_span_singleton hu] at hlo
  refine ⟨hne, Nat.le_antisymm
    (CFSGTwoPlaneIntersectionPartition.inf_finrank_le_one P _ hP hd hne) hlo, ?_⟩
  apply singular_sup B hs P _ hPs
  · exact pairPlane_singular B u z (hPs u huP u huP) hz (hPz u huP)
      ((hs z u).trans (hPz u huP))
  · intro x hx y hy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [map_add, map_smul, hPs x hx u huP, hPz x hx, smul_zero, add_zero]

omit [FiniteDimensional K V] in
theorem pairPlane_eq_implies_proportional (u : V) (j : W →ₗ[K] V) (π : V →ₗ[K] W)
    (hπ : ∀ z, π (j z) = z) (hu : π u = 0) (z z' : W)
    (he : pairPlane (K := K) u (j z) = pairPlane (K := K) u (j z')) : ∃ a : K, z = a • z' := by
  have hz : j z ∈ pairPlane (K := K) u (j z') := he ▸ Submodule.subset_span (Or.inr rfl)
  obtain ⟨a, b, hb⟩ := Submodule.mem_span_pair.mp hz
  have h := congrArg π hb
  rw [map_add, map_smul, map_smul, hu, smul_zero, zero_add, hπ, hπ] at h
  exact ⟨b, h.symm⟩

end SymmetricSubgroupAsymptotics.CFSGPolarCommonPointPlanes
