import SymmetricSubgroupAsymptotics.IrreducibleLinearSmallSpaceTransitivity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness

/-! The contragredient uses the inverse original operator, so it is a
genuine action of the same group. Its fixed functionals are exactly the
functionals invariant under the original operator. Dual coannihilation
transfers irreducibility, without identifying the module with its dual. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LinearContragredientSmallSpaceAction

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

def contragredient (ρ : G →* (V ≃ₗ[K] V)) :
    G →* (Module.Dual K V ≃ₗ[K] Module.Dual K V) where
  toFun g := (ρ g).symm.dualMap
  map_one' := by
    apply LinearEquiv.ext
    intro ℓ
    apply LinearMap.ext
    intro v
    change ℓ ((ρ 1).symm v) = ℓ v
    rw [ρ.map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro ℓ
    apply LinearMap.ext
    intro v
    change ℓ ((ρ (g * h)).symm v) = ℓ ((ρ h).symm ((ρ g).symm v))
    rw [ρ.map_mul]
    rfl

theorem fixed_iff (ρ : G →* (V ≃ₗ[K] V)) (g : G) (ℓ : Module.Dual K V) :
    contragredient ρ g ℓ = ℓ ↔ ∀ v : V, ℓ (ρ g v) = ℓ v := by
  constructor
  · intro h v
    have he := DFunLike.congr_fun h (ρ g v)
    change ℓ ((ρ g).symm (ρ g v)) = ℓ (ρ g v) at he
    rw [(ρ g).symm_apply_apply] at he
    exact he.symm
  · intro h
    apply LinearMap.ext
    intro v
    change ℓ ((ρ g).symm v) = ℓ v
    have he := h ((ρ g).symm v)
    rw [(ρ g).apply_symm_apply] at he
    exact he.symm

theorem contragredient_injective (ρ : G →* (V ≃ₗ[K] V))
    (hρ : Function.Injective ρ) : Function.Injective (contragredient ρ) := by
  intro g h he
  apply hρ
  have hs : (ρ g).symm = (ρ h).symm := by
    apply LinearEquiv.ext
    intro v
    apply Module.eval_apply_injective K
    apply LinearMap.ext
    intro ℓ
    exact congrArg
      (fun e : Module.Dual K V ≃ₗ[K] Module.Dual K V => e ℓ v) he
  simpa only [LinearEquiv.symm_symm] using congrArg LinearEquiv.symm hs

theorem irreducible_dual [FiniteDimensional K V]
    (ρ : G →* (V ≃ₗ[K] V))
    (hirr : ∀ W : Submodule K V,
      (∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule K (Module.Dual K V))
    (hW : ∀ (g : G) (ℓ : Module.Dual K V),
      ℓ ∈ W → contragredient ρ g ℓ ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let C := W.dualCoannihilator
  have hC (g : G) (v : V) (hv : v ∈ C) : ρ g v ∈ C := by
    apply (Submodule.mem_dualCoannihilator (Φ := W) (ρ g v)).mpr
    intro ℓ hℓ
    have hmem := hW g⁻¹ ℓ hℓ
    have hz := (Submodule.mem_dualCoannihilator (Φ := W) v).mp hv
      (contragredient ρ g⁻¹ ℓ) hmem
    change ℓ ((ρ g⁻¹).symm v) = 0 at hz
    have hinv : (ρ g⁻¹).symm = ρ g := by rw [ρ.map_inv]; rfl
    rw [hinv] at hz
    exact hz
  have hd : C.dualAnnihilator = W := Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases hirr C hC with hb | ht
  · right
    rw [← hd, hb, Submodule.dualAnnihilator_bot]
  · left
    rw [← hd, ht, Submodule.dualAnnihilator_top]

theorem exists_dual_map_eq_of_nonzero [Finite K] [Finite V]
    (ρ : G →* (V ≃ₗ[K] V))
    (hirr : ∀ W : Submodule K V,
      (∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hdim : 1 < Module.finrank K V)
    (hcard : Nat.card V ≤ 2 * Module.finrank K V + 2)
    (ℓ m : Module.Dual K V) (hℓ : ℓ ≠ 0) (hm : m ≠ 0) :
    ∃ g : G, contragredient ρ g ℓ = m := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  letI : Finite (Module.Dual K V) := Finite.of_injective
    (fun ℓ : Module.Dual K V => (ℓ : V → K)) DFunLike.coe_injective
  have hd : Module.finrank K (Module.Dual K V) = Module.finrank K V :=
    Subspace.dual_finrank_eq
  have hc : Nat.card (Module.Dual K V) = Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := Module.Dual K V), hd,
      ← Module.natCard_eq_pow_finrank (K := K) (V := V)]
  apply IrreducibleLinearSmallSpaceTransitivity.exists_map_eq_of_nonzero
    (contragredient ρ) (irreducible_dual ρ hirr)
  · rwa [hd]
  · rwa [hc, hd]
  · exact hℓ
  · exact hm

end SymmetricSubgroupAsymptotics.LinearContragredientSmallSpaceAction
