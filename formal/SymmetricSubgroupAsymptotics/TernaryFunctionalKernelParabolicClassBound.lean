import SymmetricSubgroupAsymptotics.InvariantFunctionalKernelScalarAction
import SymmetricSubgroupAsymptotics.TernaryThreeFunctionalStabilizerClassBound
import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.Data.Fintype.Units

/-! A ternary three-space automorphism group preserving an actual
functional kernel retains its scalar quotient of order at most two.
The actual scalar kernel fixes the functional and has the affine-nine
bound39, hence the SAME group has at most78 conjugacy classes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFunctionalKernelParabolicClassBound
open LinearContragredientSmallSpaceAction AbelianSemidirectDualClassIdentity

variable {K : Type*} {N G : Type} [Field K] [CommGroup N] [Group G]
    [Module K (Additive N)] [Finite K] [Finite N] [Finite G]

theorem class_card_le_seventyEight (hK : Nat.card K=3) (hN : Nat.card N=27)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n)=Additive.ofMul (φ g n))
    (ℓ : Module.Dual K (Additive N)) (hℓ : ℓ≠0)
    (hstable : ∀ (g : G) (v : Additive N), ℓ (ρ g v)=0 ↔ ℓ v=0) :
    Nat.card (ConjClasses G)≤78 := by
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hℓ
  let a : Additive N := (ℓ v)⁻¹ • v
  have ha : ℓ a=1 := by
    dsimp only [a]
    rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hv]
  let σ := InvariantFunctionalKernelScalarAction.scalarHom ρ ℓ a ha hstable
  let S := σ.ker
  let η : S →* MulAut N := φ.comp S.subtype
  let τ : S →* (Additive N ≃ₗ[K] Additive N) := ρ.comp S.subtype
  have hη : Function.Injective η := hφ.comp Subtype.val_injective
  have hcompatS (g : S) (n : N) : τ g (Additive.ofMul n)=Additive.ofMul (η g n) :=
    hcompat g.val n
  have hfixS (g : S) (w : Additive N) : ℓ (τ g w)=ℓ w :=
    InvariantFunctionalKernelScalarAction.kernel_fixes_functional ρ ℓ a ha hstable g w
  have htop : dualStabilizer τ ℓ=⊤ := by
    apply Subgroup.ext
    intro g
    change contragredient τ g ℓ=ℓ ↔ True
    exact iff_of_true ((fixed_iff τ g ℓ).mpr (hfixS g)) trivial
  have hsub := TernaryThreeFunctionalStabilizerClassBound.class_card_le_thirtyNine
    hK hN η hη τ hcompatS ℓ hℓ
  rw [htop] at hsub
  have hS : Nat.card (ConjClasses S)≤39 :=
    (Nat.card_le_card_of_surjective
      (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).toMonoidHom)
      (ConjClasses.map_surjective Subgroup.topEquiv.surjective)).trans hsub
  have hQ : Nat.card (ConjClasses σ.range)≤2 := by
    calc
      _≤Nat.card σ.range := Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
      _≤Nat.card Kˣ := Nat.card_le_card_of_injective σ.range.subtype Subtype.val_injective
      _=2 := by rw [Nat.card_units,hK]
  exact (conjugacyClass_card_le_kernel_mul_range σ).trans
    ((Nat.mul_le_mul hS hQ).trans (by decide : (39:ℕ)*2≤78))

end SymmetricSubgroupAsymptotics.TernaryFunctionalKernelParabolicClassBound
