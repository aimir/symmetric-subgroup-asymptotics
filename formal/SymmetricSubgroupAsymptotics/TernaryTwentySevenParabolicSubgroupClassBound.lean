import SymmetricSubgroupAsymptotics.TernaryThreeInvariantSubspaceClassBound
import SymmetricSubgroupAsymptotics.TernaryThreeFunctionalStabilizerClassBound
import SymmetricSubgroupAsymptotics.AbelianSemidirectDualStabilizerClassBound
import SymmetricSubgroupAsymptotics.AbelianSemidirectPlaneKernelClassBound
import SymmetricSubgroupAsymptotics.OrderNineAutomorphismClassBound

/-! A uniform actual ternary27 subgroup bound. Full translation
intersection uses the SAME nonzero dual stabilizers. A nontrivial proper
intersection is an actual line or plane and its projected complement
retains the scalar quotient; a trivial intersection keeps the original
linear-group order bound. No subgroup splitting or subgroup census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryTwentySevenParabolicSubgroupClassBound
open SemidirectSubgroupOverKernel
open OrderNineAutomorphismClassBound (automorphismLinear automorphismLinear_injective)
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {N G : Type} [CommGroup N] [Group G] [Finite N] [Finite G]
    [Module (ZMod 3) (Additive N)]

private theorem complement_class_card_le (hN : Nat.card N=27)
    (φ : G →* MulAut N) (hφ : Function.Injective φ) :
    Nat.card (ConjClasses G)≤11232 := by
  let ρ := (automorphismLinear (N:=N)).comp φ
  have hρ : Function.Injective ρ := (automorphismLinear_injective (N:=N)).comp hφ
  letI : Finite (Additive N ≃ₗ[ZMod 3] Additive N) := Finite.of_injective
    (fun f : Additive N ≃ₗ[ZMod 3] Additive N => (f : Additive N → Additive N))
    DFunLike.coe_injective
  exact (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
    ((Nat.card_le_card_of_injective ρ hρ).trans_eq
      (TernaryThreeInvariantSubspaceClassBound.linearEquiv_card_eq_elevenTwoThirtyTwo
        (K:=ZMod 3) (V:=Additive N) (Nat.card_zmod 3) hN))

omit [Module (ZMod 3) (Additive N)] in
private theorem proper_subgroup_card_le_nine (hN : Nat.card N=27)
    (C : Subgroup N) (hC : C≠⊤) : Nat.card C≤9 := by
  have hd : Nat.card C∣(3:ℕ)^3 := by
    simpa only [hN,show (3:ℕ)^3=27 by decide] using C.card_subgroup_dvd_card
  obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have hi2 : i≤2 := by
    by_contra h
    have hi3 : i=3 := by omega
    apply hC
    apply C.eq_top_of_card_eq
    simpa only [he,hi3,show (3:ℕ)^3=27 by decide] using hN.symm
  exact he.le.trans (by
    calc
      (3:ℕ)^i≤3^2 := Nat.pow_le_pow_right (by decide) hi2
      _=9 := by decide)

theorem class_card_le_seventyEight_of_invariant_proper_subgroup
    (hN : Nat.card N=27) (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (C : Subgroup N) (hCb : C≠⊥) (hCt : C≠⊤)
    (hstable : ∀ (g : G) (n : N), φ g n∈C ↔ n∈C) :
    Nat.card (ConjClasses G)≤78 := by
  letI : FiniteDimensional (ZMod 3) (Additive N) := Module.Finite.of_finite
  let ρ := (automorphismLinear (N:=N)).comp φ
  have hρ : Function.Injective ρ := (automorphismLinear_injective (N:=N)).comp hφ
  let W : Submodule (ZMod 3) (Additive N) :=
    AddSubgroup.toZModSubmodule 3 (Subgroup.toAddSubgroup C)
  let eW : W ≃ C := {
    toFun := fun v => ⟨v.val.toMul,v.property⟩
    invFun := fun n => ⟨Additive.ofMul n.val,n.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcardW : Nat.card W=Nat.card C := Nat.card_congr eW
  have hd : Nat.card C∣(3:ℕ)^3 := by
    simpa only [hN,show (3:ℕ)^3=27 by decide] using C.card_subgroup_dvd_card
  obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have hi0 : i≠0 := by
    intro hz
    apply hCb
    exact C.eq_bot_of_card_eq (by simp only [he,hz,pow_zero])
  have hi3 : i≠3 := by
    intro hz
    apply hCt
    apply C.eq_top_of_card_eq
    simpa only [he,hz,show (3:ℕ)^3=27 by decide] using hN.symm
  have hdimW : Module.finrank (ZMod 3) W=i := by
    have hh := Module.natCard_eq_pow_finrank (K:=ZMod 3) (V:=W)
    rw [Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 2≤(3:ℕ))
      (hh.symm.trans (hcardW.trans he))
  have hW (g : G) (v : Additive N) (hv : v∈W) : ρ g v∈W := by
    change φ g v.toMul∈C
    exact (hstable g v.toMul).mpr hv
  by_cases hi1 : i=1
  · exact TernaryThreeInvariantSubspaceClassBound.class_card_le_seventyEight_of_invariant_line
      (K:=ZMod 3) (V:=Additive N) (G:=G) (Nat.card_zmod 3) hN ρ hρ W (hdimW.trans hi1) hW
  · have hi2 : i=2 := by omega
    exact TernaryThreeInvariantSubspaceClassBound.class_card_le_seventyEight_of_invariant_plane
      (K:=ZMod 3) (V:=Additive N) (G:=G) (Nat.card_zmod 3) hN ρ hρ W (hdimW.trans hi2) hW

theorem class_card_le_twelveTwoFortySeven (hN : Nat.card N=27)
    (φ : G →* MulAut N) (hφ : Function.Injective φ) :
    Nat.card (ConjClasses (N ⋊[φ] G))≤12247 := by
  letI : FiniteDimensional (ZMod 3) (Additive N) := Module.Finite.of_finite
  let ρ := (automorphismLinear (N:=N)).comp φ
  have hcompat (g : G) (n : N) : ρ g (Additive.ofMul n)=Additive.ofMul (φ g n) := rfl
  have hdual : Nat.card (Module.Dual (ZMod 3) (Additive N))=27 := by
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 3),Subspace.dual_finrank_eq,
      ←Module.natCard_eq_pow_finrank (K:=ZMod 3) (V:=Additive N)]
    exact hN
  have hs := AbelianSemidirectDualStabilizerClassBound.class_card_le_add_punctured_bound
    φ ρ hcompat 39 (TernaryThreeFunctionalStabilizerClassBound.class_card_le_thirtyNine
      (Nat.card_zmod 3) hN φ hφ ρ hcompat)
  have ht := complement_class_card_le hN φ hφ
  rw [hdual] at hs
  omega

theorem subgroup_class_card_le_twelveTwoFortySeven (hN : Nat.card N=27)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] G)) : Nat.card (ConjClasses L)≤12247 := by
  letI : Finite (N ⋊[φ] G) := Finite.of_equiv (N×G) SemidirectProduct.equivProd.symm
  let C := L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] G))
  by_cases hCt : C=⊤
  · have hfull (n : N) : SemidirectProduct.inl n∈L := by
      have hn : n∈C := by rw [hCt]; trivial
      exact hn
    let R := Projected φ L
    let ψ : R →* MulAut N := φ.comp R.subtype
    let e := overKernelEquiv φ L hfull
    letI : Finite (N ⋊[ψ] R) := Finite.of_equiv L e.toEquiv
    have hc : Nat.card (ConjClasses L)≤Nat.card (ConjClasses (N ⋊[ψ] R)) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    exact hc.trans (class_card_le_twelveTwoFortySeven hN ψ (hφ.comp Subtype.val_injective))
  · let π : L →* G := (SemidirectProduct.rightHom : (N ⋊[φ] G) →* G).comp L.subtype
    let ψ : π.range →* MulAut N := φ.comp π.range.subtype
    have hψ : Function.Injective ψ := hφ.comp Subtype.val_injective
    have hkcard := AbelianSemidirectSubgroupCentralizerBound.kernel_card_le_intersection φ L
    by_cases hCb : C=⊥
    · have hcsmall : Nat.card C≤1 := by rw [hCb,Subgroup.card_bot]
      have hk : Nat.card (ConjClasses π.ker)≤1 :=
        (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
          (hkcard.trans hcsmall)
      have ht := complement_class_card_le hN ψ hψ
      exact ((conjugacyClass_card_le_kernel_mul_range π).trans
        (Nat.mul_le_mul hk ht)).trans (by decide : (1:ℕ)*11232≤12247)
    · have hk : Nat.card (ConjClasses π.ker)≤9 :=
        (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
          (hkcard.trans (proper_subgroup_card_le_nine hN C hCt))
      have hstable : ∀ (g : π.range) (n : N), ψ g n∈C ↔ n∈C :=
        AbelianSemidirectPlaneKernelClassBound.projected_preserves_intersection φ L
      have ht := class_card_le_seventyEight_of_invariant_proper_subgroup
        hN ψ hψ C hCb hCt hstable
      exact ((conjugacyClass_card_le_kernel_mul_range π).trans
        (Nat.mul_le_mul hk ht)).trans (by decide : (9:ℕ)*78≤12247)

end SymmetricSubgroupAsymptotics.TernaryTwentySevenParabolicSubgroupClassBound
