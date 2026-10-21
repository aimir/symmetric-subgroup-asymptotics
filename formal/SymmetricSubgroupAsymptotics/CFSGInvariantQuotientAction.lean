import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! Actual linear automorphisms preserving a submodule in both directions
act on its literal quotient. A surjective linear map transports that action
to its target, with an exact intertwining formula. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGInvariantQuotientAction
variable {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V]

def stabilizer (S : Submodule R M) : Subgroup (M ≃ₗ[R] M) where
  carrier := {g | (∀ x ∈ S, g x ∈ S) ∧ ∀ x ∈ S, g.symm x ∈ S}
  one_mem' := ⟨fun _ hx => hx, fun _ hx => hx⟩
  mul_mem' := by
    rintro g h ⟨hg, hgi⟩ ⟨hh, hhi⟩
    exact ⟨fun x hx => hg (h x) (hh x hx),
      fun x hx => hhi (g.symm x) (hgi x hx)⟩
  inv_mem' := by
    rintro g ⟨hg, hgi⟩
    exact ⟨hgi, hg⟩

def quotientEquiv (S : Submodule R M) (g : stabilizer S) :
    (M ⧸ S) ≃ₗ[R] (M ⧸ S) where
  __ := S.mapQ S g.val.toLinearMap g.property.1
  invFun := S.mapQ S g.val.symm.toLinearMap g.property.2
  left_inv := by
    intro q
    obtain ⟨x, rfl⟩ := S.mkQ_surjective q
    change Submodule.Quotient.mk (g.val.symm (g.val x)) = Submodule.Quotient.mk x
    rw [LinearEquiv.symm_apply_apply]
  right_inv := by
    intro q
    obtain ⟨x, rfl⟩ := S.mkQ_surjective q
    change Submodule.Quotient.mk (g.val (g.val.symm x)) = Submodule.Quotient.mk x
    rw [LinearEquiv.apply_symm_apply]

@[simp] theorem quotientEquiv_mk (S : Submodule R M) (g : stabilizer S) (x : M) :
    quotientEquiv S g (S.mkQ x) = S.mkQ (g.val x) := rfl

def quotientAction (S : Submodule R M) : stabilizer S →* ((M ⧸ S) ≃ₗ[R] (M ⧸ S)) where
  toFun := quotientEquiv S
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := S.mkQ_surjective q
    rfl
  map_mul' := by
    intro g h
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := S.mkQ_surjective q
    rfl

def automorphismCongr (e : M ≃ₗ[R] V) : (M ≃ₗ[R] M) ≃* (V ≃ₗ[R] V) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv R M).symm.trans
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv R V)

@[simp] theorem automorphismCongr_apply (e : M ≃ₗ[R] V) (g : M ≃ₗ[R] M) (x : V) :
    automorphismCongr e g x = e (g (e.symm x)) := rfl

def descendedAction (β : M →ₗ[R] V) (hβ : Function.Surjective β) :
    stabilizer (LinearMap.ker β) →* (V ≃ₗ[R] V) :=
  (automorphismCongr (β.quotKerEquivOfSurjective hβ)).toMonoidHom.comp
    (quotientAction (LinearMap.ker β))

theorem descendedAction_intertwines (β : M →ₗ[R] V) (hβ : Function.Surjective β)
    (g : stabilizer (LinearMap.ker β)) (x : M) :
    descendedAction β hβ g (β x) = β (g.val x) := by
  change automorphismCongr (β.quotKerEquivOfSurjective hβ)
    (quotientEquiv (LinearMap.ker β) g) (β x) = _
  rw [automorphismCongr_apply, LinearMap.quotKerEquivOfSurjective_symm_apply]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk β hβ (g.val x)

theorem descendedAction_unique (β : M →ₗ[R] V) (hβ : Function.Surjective β)
    (g : stabilizer (LinearMap.ker β)) (h : V ≃ₗ[R] V)
    (hh : ∀ x : M, h (β x) = β (g.val x)) : descendedAction β hβ g = h := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hβ y
  exact (descendedAction_intertwines β hβ g x).trans (hh x).symm

end SymmetricSubgroupAsymptotics.CFSGInvariantQuotientAction
