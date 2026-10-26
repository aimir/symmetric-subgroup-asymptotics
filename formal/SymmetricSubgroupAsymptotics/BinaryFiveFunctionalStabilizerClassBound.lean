import SymmetricSubgroupAsymptotics.BinaryIndexTwoSixteenAutomorphismClassBound
import SymmetricSubgroupAsymptotics.BinaryFunctionalStabilizerClassBound

/-! Actual nonzero functional stabilizers on a binary five-space have
affine-sixteen charts. No nonzero-orbit transitivity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFiveFunctionalStabilizerClassBound
open BinaryFunctionalStabilizerClassBound AbelianSemidirectDualClassIdentity
open LinearContragredientSmallSpaceAction

variable {N G : Type} [CommGroup N] [Group G] [Finite N] [Finite G]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive N)]

theorem functionalKernel_card_sixteen (hp : p=2) (hN : Nat.card N=32)
    (ℓ : Module.Dual (ZMod p) (Additive N)) (hℓ : ℓ≠0) :
    Nat.card (functionalKernel ℓ)=16 := by
  letI : FiniteDimensional (ZMod p) (Additive N) := Module.Finite.of_finite
  have hK : Nat.card (ZMod p)=2 := (Nat.card_zmod p).trans hp
  have hd : Module.finrank (ZMod p) (Additive N)=5 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive N)
    change Nat.card N=Nat.card (ZMod p)^Module.finrank (ZMod p) (Additive N) at hc
    rw [hN,hK] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ (2:ℕ)) hc.symm
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hℓ
  have hsurj : Function.Surjective ℓ := by
    intro c
    refine ⟨(c/ℓ v) • v,?_⟩
    rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hv]
  have hrange : ℓ.range=⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := ℓ.finrank_range_add_finrank_ker
  rw [hrange,finrank_top,CommSemiring.finrank_self,hd] at hdim
  have hkdim : Module.finrank (ZMod p) ℓ.ker=4 := by omega
  let e : functionalKernel ℓ ≃ ℓ.ker := {
    toFun := fun n => ⟨Additive.ofMul n.val,n.property⟩
    invFun := fun v => ⟨v.val.toMul,v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := ZMod p) (V := ℓ.ker),hK,hkdim]
  decide

theorem class_card_le_sevenSeventyTwo (hp : p=2) (hN : Nat.card N=32)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (ρ : G →* (Additive N ≃ₗ[ZMod p] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n)=Additive.ofMul (φ g n))
    (ℓ : Module.Dual (ZMod p) (Additive N)) (hℓ : ℓ≠0) :
    Nat.card (ConjClasses (dualStabilizer ρ ℓ)) ≤ 772 := by
  let C := functionalKernel ℓ
  have hC : Nat.card C=16 := functionalKernel_card_sixteen hp hN ℓ hℓ
  have hindex : C.index=2 := by
    have hh := C.card_mul_index
    rw [hC,hN] at hh
    omega
  let η : dualStabilizer ρ ℓ →* MulAut N := φ.comp (dualStabilizer ρ ℓ).subtype
  have hη : Function.Injective η := hφ.comp Subtype.val_injective
  have hstable (g : dualStabilizer ρ ℓ) (n : N) : η g n∈C ↔ n∈C := by
    have hg : contragredient ρ g.val ℓ=ℓ := g.property
    have he := (fixed_iff ρ g.val ℓ).mp hg (Additive.ofMul n)
    rw [hcompat] at he
    change ℓ (Additive.ofMul (φ g.val n))=0 ↔ ℓ (Additive.ofMul n)=0
    rw [he]
  exact BinaryIndexTwoSixteenAutomorphismClassBound.class_card_le_sevenSeventyTwo
    hp C hC hindex η hη hstable

end SymmetricSubgroupAsymptotics.BinaryFiveFunctionalStabilizerClassBound
