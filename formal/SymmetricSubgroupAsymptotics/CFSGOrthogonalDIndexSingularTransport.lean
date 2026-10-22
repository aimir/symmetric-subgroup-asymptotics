import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularParity

/-! Actual linear isometries transport the singular spaces and their
intersection dimensions. These facts will make the proved intersection
parity a genuine component invariant, rather than a named assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularTransport
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem preserves_polar (Q : QuadraticForm K V) (f : V ≃ₗ[K] V)
    (hf : ∀ x, Q (f x) = Q x) (x y : V) :
    Q.polarBilin (f x) (f y) = Q.polarBilin x y := by
  change Q (f x + f y) - Q (f x) - Q (f y) = Q (x + y) - Q x - Q y
  rw [← map_add, hf, hf, hf]

theorem mem_orthogonal_map_iff (Q : QuadraticForm K V) (f : V ≃ₗ[K] V)
    (hf : ∀ x, Q (f x) = Q x) (P : Submodule K V) (x : V) :
    f x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (P.map f.toLinearMap) ↔
      x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin P := by
  constructor
  · intro hx y hy
    have h := hx (f y) ⟨y, hy, rfl⟩
    change Q.polarBilin (f y) (f x) = 0 at h
    rw [preserves_polar Q f hf] at h
    exact h
  · intro hx y hy
    obtain ⟨z, hz, rfl⟩ := hy
    change Q.polarBilin (f z) (f x) = 0
    rw [preserves_polar Q f hf]
    exact hx z hz

theorem orthogonal_map (Q : QuadraticForm K V) (f : V ≃ₗ[K] V)
    (hf : ∀ x, Q (f x) = Q x) (P : Submodule K V) :
    LinearMap.BilinForm.orthogonal Q.polarBilin (P.map f.toLinearMap) =
      (LinearMap.BilinForm.orthogonal Q.polarBilin P).map f.toLinearMap := by
  ext z
  obtain ⟨x, rfl⟩ := f.surjective z
  rw [mem_orthogonal_map_iff Q f hf]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact (f.injective he) ▸ hy

theorem map_self_orthogonal (Q : QuadraticForm K V) (f : V ≃ₗ[K] V)
    (hf : ∀ x, Q (f x) = Q x) (P : Submodule K V)
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P) :
    LinearMap.BilinForm.orthogonal Q.polarBilin (P.map f.toLinearMap) = P.map f.toLinearMap := by
  rw [orthogonal_map Q f hf P, hP]

theorem map_singular (Q : QuadraticForm K V) (f : V ≃ₗ[K] V)
    (hf : ∀ x, Q (f x) = Q x) (P : Submodule K V)
    (hP : ∀ x : P, Q (x : V) = 0) (x : P.map f.toLinearMap) : Q (x : V) = 0 := by
  obtain ⟨y, hy, he⟩ := x.property
  change f y = x.val at he
  rw [← he, hf]
  exact hP ⟨y, hy⟩

theorem intersection_map_finrank [FiniteDimensional K V]
    (f : V ≃ₗ[K] V) (P L : Submodule K V) :
    Module.finrank K ↥(P.map f.toLinearMap ⊓ L.map f.toLinearMap) =
      Module.finrank K ↥(P ⊓ L) := by
  rw [← Submodule.map_inf f.toLinearMap f.injective]
  exact f.finrank_map_eq (P ⊓ L)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularTransport
