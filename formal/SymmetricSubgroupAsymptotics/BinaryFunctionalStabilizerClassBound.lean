import SymmetricSubgroupAsymptotics.AbelianSemidirectDualClassIdentity
import SymmetricSubgroupAsymptotics.AutomorphismProperSubgroupComplementAction
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! An actual stabilizer of a nonzero binary functional preserves its
literal kernel of order four. Restricting the original faithful action
to that same stabilizer gives a faithful action on the four-element
complement, and hence at most five conjugacy classes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFunctionalStabilizerClassBound
open AbelianSemidirectDualClassIdentity LinearContragredientSmallSpaceAction

variable {K : Type*} {N G : Type} [Field K] [CommGroup N] [Group G]
    [Module K (Additive N)]

def functionalKernel (ℓ : Module.Dual K (Additive N)) : Subgroup N where
  carrier := {n : N | ℓ (Additive.ofMul n) = 0}
  one_mem' := ℓ.map_zero
  mul_mem' ha hb := by
    change ℓ (Additive.ofMul _ + Additive.ofMul _) = 0
    rw [map_add, ha, hb, add_zero]
  inv_mem' ha := by
    change ℓ (-Additive.ofMul _) = 0
    rw [map_neg, ha, neg_zero]

theorem functionalKernel_card_four [Finite N]
    (hK : Nat.card K = 2) (hN : Nat.card N = 8)
    (ℓ : Module.Dual K (Additive N)) (hℓ : ℓ ≠ 0) :
    Nat.card (functionalKernel ℓ) = 4 := by
  letI : FiniteDimensional K (Additive N) := Module.Finite.of_finite
  have hd : Module.finrank K (Additive N) = 3 := by
    have hc := Module.natCard_eq_pow_finrank (K := K) (V := Additive N)
    change Nat.card N = Nat.card K ^ Module.finrank K (Additive N) at hc
    rw [hN, hK] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hc.symm
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hℓ
  have hsurj : Function.Surjective ℓ := by
    intro c
    refine ⟨(c / ℓ v) • v, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  have hrange : ℓ.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := ℓ.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, CommSemiring.finrank_self, hd] at hdim
  have hkdim : Module.finrank K ℓ.ker = 2 := by omega
  let e : functionalKernel ℓ ≃ ℓ.ker := {
    toFun := fun n => ⟨Additive.ofMul n.val, n.property⟩
    invFun := fun v => ⟨v.val.toMul, v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K) (V := ℓ.ker), hK, hkdim]
  decide

theorem class_card_le_five [Finite K] [Finite N] [Finite G]
    (hK : Nat.card K = 2) (hN : Nat.card N = 8)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n) = Additive.ofMul (φ g n))
    (ℓ : Module.Dual K (Additive N)) (hℓ : ℓ ≠ 0) :
    Nat.card (ConjClasses (dualStabilizer ρ ℓ)) ≤ 5 := by
  let C := functionalKernel ℓ
  have hC : Nat.card C = 4 := functionalKernel_card_four hK hN ℓ hℓ
  have hproper : C ≠ ⊤ := by
    intro he
    rw [he, Subgroup.card_top, hN] at hC
    omega
  have hcomplement : Nat.card {n : N // n ∉ C} = 4 := by
    have hs : Nat.card C + Nat.card {n : N // n ∉ C} = Nat.card N := by
      rw [← Nat.card_sum]
      exact Nat.card_congr (Equiv.sumCompl (fun n : N => n ∈ C))
    omega
  let η : dualStabilizer ρ ℓ →* MulAut N := φ.comp (dualStabilizer ρ ℓ).subtype
  have hη : Function.Injective η := hφ.comp Subtype.val_injective
  have hstable (g : dualStabilizer ρ ℓ) (n : N) : η g n ∈ C ↔ n ∈ C := by
    have hg : contragredient ρ g.val ℓ = ℓ := g.property
    have he := (fixed_iff ρ g.val ℓ).mp hg (Additive.ofMul n)
    rw [hcompat] at he
    change ℓ (Additive.ofMul (φ g.val n)) = 0 ↔ ℓ (Additive.ofMul n) = 0
    rw [he]
  exact AutomorphismProperSubgroupComplementAction.class_card_le_five_of_complement_card_four
    C hproper η hη hstable hcomplement

end SymmetricSubgroupAsymptotics.BinaryFunctionalStabilizerClassBound
