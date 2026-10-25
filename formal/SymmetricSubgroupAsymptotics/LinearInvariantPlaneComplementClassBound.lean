import SymmetricSubgroupAsymptotics.AutomorphismProperSubgroupComplementAction
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.TypeTags.Finite

/-! A faithful linear action preserving an actual four-element plane in
an eight-element space has at most five conjugacy classes. The same
action is transported to the multiplicative type tag and acts faithfully
on the literal four-element complement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LinearInvariantPlaneComplementClassBound

variable {K : Type*} {V G : Type} [Field K] [AddCommGroup V] [Module K V] [Group G]

def multiplicativeAction (ρ : G →* (V ≃ₗ[K] V)) : G →* MulAut (Multiplicative V) where
  toFun g := (ρ g).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (ρ 1 v.toAdd) = v
    rw [ρ.map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (ρ (g * h) v.toAdd) =
      Multiplicative.ofAdd (ρ g (ρ h v.toAdd))
    rw [ρ.map_mul]
    rfl

theorem multiplicativeAction_injective (ρ : G →* (V ≃ₗ[K] V))
    (hρ : Function.Injective ρ) : Function.Injective (multiplicativeAction ρ) := by
  intro g h he
  apply hρ
  apply LinearEquiv.ext
  intro v
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun he (Multiplicative.ofAdd v))

theorem class_card_le_five [Finite V] [Finite G]
    (hV : Nat.card V = 8) (ρ : G →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ)
    (W : Submodule K V) (hW : Nat.card W = 4)
    (hstable : ∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) :
    Nat.card (ConjClasses G) ≤ 5 := by
  let C : Subgroup (Multiplicative V) := W.toAddSubgroup.toSubgroup
  let e : C ≃ W := {
    toFun := fun v => ⟨v.val.toAdd, v.property⟩
    invFun := fun v => ⟨Multiplicative.ofAdd v.val, v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hC : Nat.card C = 4 := (Nat.card_congr e).trans hW
  have hproper : C ≠ ⊤ := by
    intro he
    rw [he, Subgroup.card_top] at hC
    change Nat.card V = 4 at hC
    omega
  have hcomplement : Nat.card {v : Multiplicative V // v ∉ C} = 4 := by
    have hs : Nat.card C + Nat.card {v : Multiplicative V // v ∉ C} = Nat.card V := by
      rw [← Nat.card_sum]
      exact Nat.card_congr (Equiv.sumCompl (fun v : Multiplicative V => v ∈ C))
    omega
  have hpreserve (g : G) (v : Multiplicative V) :
      multiplicativeAction ρ g v ∈ C ↔ v ∈ C := by
    change ρ g v.toAdd ∈ W ↔ v.toAdd ∈ W
    constructor
    · intro hv
      have hh := hstable g⁻¹ (ρ g v.toAdd) hv
      have hc : ρ g⁻¹ (ρ g v.toAdd) = v.toAdd := by
        change (ρ g⁻¹ * ρ g) v.toAdd = v.toAdd
        rw [← ρ.map_mul, inv_mul_cancel, ρ.map_one]
        rfl
      rwa [hc] at hh
    · exact hstable g v.toAdd
  exact AutomorphismProperSubgroupComplementAction.class_card_le_five_of_complement_card_four
    C hproper (multiplicativeAction ρ) (multiplicativeAction_injective ρ hρ) hpreserve hcomplement

end SymmetricSubgroupAsymptotics.LinearInvariantPlaneComplementClassBound
