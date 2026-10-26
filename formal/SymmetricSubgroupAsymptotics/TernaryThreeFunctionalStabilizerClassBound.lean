import SymmetricSubgroupAsymptotics.FunctionalKernelAffineAutomorphismChart
import SymmetricSubgroupAsymptotics.NineElementSemidirectSubgroupClassGap

/-! Every actual nonzero functional stabilizer on a ternary three-space
has a faithful affine chart on its literal nine-element kernel. The
same stabilizer therefore has at most39 conjugacy classes. There is no
assumption of transitivity on nonzero functionals or supplied splitting. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryThreeFunctionalStabilizerClassBound
open BinaryFunctionalStabilizerClassBound LinearContragredientSmallSpaceAction
open AbelianSemidirectDualClassIdentity

variable {K : Type*} {N G : Type} [Field K] [CommGroup N] [Group G]
    [Module K (Additive N)]

theorem functionalKernel_card_nine [Finite N]
    (hK : Nat.card K=3) (hN : Nat.card N=27)
    (ℓ : Module.Dual K (Additive N)) (hℓ : ℓ≠0) :
    Nat.card (functionalKernel ℓ)=9 := by
  letI : FiniteDimensional K (Additive N) := Module.Finite.of_finite
  have hd : Module.finrank K (Additive N)=3 := by
    have hc := Module.natCard_eq_pow_finrank (K:=K) (V:=Additive N)
    change Nat.card N=Nat.card K^Module.finrank K (Additive N) at hc
    rw [hN,hK] at hc
    exact Nat.pow_right_injective (by decide : 2≤(3:ℕ)) hc.symm
  obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hℓ
  have hsurj : Function.Surjective ℓ := by
    intro c
    refine ⟨(c/ℓ v) • v,?_⟩
    rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hv]
  have hrange : ℓ.range=⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := ℓ.finrank_range_add_finrank_ker
  rw [hrange,finrank_top,CommSemiring.finrank_self,hd] at hdim
  have hkdim : Module.finrank K ℓ.ker=2 := by omega
  let e : functionalKernel ℓ ≃ ℓ.ker := {
    toFun := fun n => ⟨Additive.ofMul n.val,n.property⟩
    invFun := fun v => ⟨v.val.toMul,v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K:=K) (V:=ℓ.ker),hK,hkdim]
  decide

theorem class_card_le_thirtyNine [Finite K] [Finite N] [Finite G]
    (hK : Nat.card K=3) (hN : Nat.card N=27)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n)=Additive.ofMul (φ g n))
    (ℓ : Module.Dual K (Additive N)) (hℓ : ℓ≠0) :
    Nat.card (ConjClasses (dualStabilizer ρ ℓ))≤39 := by
  let S := dualStabilizer ρ ℓ
  let C := functionalKernel ℓ
  have hC : Nat.card C=9 := functionalKernel_card_nine hK hN ℓ hℓ
  let η : S →* MulAut N := φ.comp S.subtype
  let τ : S →* (Additive N ≃ₗ[K] Additive N) := ρ.comp S.subtype
  have hη : Function.Injective η := hφ.comp Subtype.val_injective
  have hcompatS (g : S) (n : N) : τ g (Additive.ofMul n)=Additive.ofMul (η g n) :=
    hcompat g.val n
  have hfixS (g : S) (v : Additive N) : ℓ (τ g v)=ℓ v :=
    (fixed_iff ρ g.val ℓ).mp g.property v
  obtain ⟨a,ha⟩ := FunctionalKernelAffineAutomorphismChart.exists_injective_affineHom
    η τ hcompatS ℓ hfixS hη hℓ
  letI : Finite (MulAut C) := Finite.of_injective
    (fun f : MulAut C => (f : C → C)) DFunLike.coe_injective
  let f := FunctionalKernelAffineAutomorphismChart.affineHom η τ hcompatS ℓ hfixS a
  have hf : Function.Injective f := ha
  let e := MonoidHom.ofInjective hf
  letI : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc : Nat.card (ConjClasses S)≤Nat.card (ConjClasses f.range) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact hc.trans (NineElementSemidirectSubgroupClassGap.subgroup_class_card_le_thirtyNine
    hC (MonoidHom.id (MulAut C)) (fun _ _ h => h) f.range)

end SymmetricSubgroupAsymptotics.TernaryThreeFunctionalStabilizerClassBound
