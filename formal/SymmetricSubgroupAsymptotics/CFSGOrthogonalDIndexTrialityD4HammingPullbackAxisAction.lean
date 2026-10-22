import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingAxisAction

/-! Equivariant coordinates transport ENTIRE original fibres under
axis actions, so the original q-cliques are not replaced by points. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
variable {X Y : Type*}

theorem image_preimage_of_equivariant (e : Equiv.Perm X) (f : Equiv.Perm Y)
    (rho : X → Y) (h : ∀ x, f (rho x) = rho (e x)) (S : Set Y) :
    e '' (rho ⁻¹' S) = rho ⁻¹' (f '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rho x, hx, h x⟩
  · rintro ⟨z, hz, hzy⟩
    have hrho : rho (e.symm y) = z := by
      apply f.injective
      exact (h (e.symm y)).trans ((congrArg rho (e.apply_symm_apply y)).trans hzy.symm)
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change rho (e.symm y) ∈ S
    rw [hrho]
    exact hz

variable {I : Type*} [DecidableEq I] [Finite I] {D : I → Type*}
  [∀ i, Nontrivial (D i)]

theorem image_pullback_coordinateAxis (e : Equiv.Perm X)
    (f : Equiv.Perm (∀ j, D j)) (rho : X → (∀ j, D j))
    (h : ∀ x, f (rho x) = rho (e x))
    (hf : ∀ x y, ClosedAdjacent (f x) (f y) ↔ ClosedAdjacent x y)
    (base x : ∀ j, D j) (i : I) :
    e '' (rho ⁻¹' CoordinateAxis i x) =
      rho ⁻¹' CoordinateAxis (directionPermutation f hf base i) (f x) := by
  rw [image_preimage_of_equivariant e f rho h, image_coordinateAxis f hf base x i]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4HammingEdges
