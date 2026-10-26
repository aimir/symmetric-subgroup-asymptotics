import SymmetricSubgroupAsymptotics.BinaryFiveFunctionalStabilizerClassBound
import SymmetricSubgroupAsymptotics.AbelianSemidirectDualStabilizerClassBound
import SymmetricSubgroupAsymptotics.BinaryThirtyTwoElementSemidirectClassGap

/-! The same index-two parabolic recursion on32 binary translations.
Every subgroup retains its own translation intersection and projection;
the full-kernel case uses its actual dual stabilizers. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryThirtyTwoParabolicSubgroupClassBound
open BinaryFiveElementSemidirectClassBound (automorphismLinear automorphismLinear_injective)
open SemidirectSubgroupOverKernel

variable {N G : Type} [CommGroup N] [Group G] [Finite N] [Finite G]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive N)]

private theorem projected_class_card_le (hp : p=2) (hN : Nat.card N=32)
    (φ : G →* MulAut N) (hφ : Function.Injective φ) :
    Nat.card (ConjClasses G) ≤ 43905 := by
  let ρ : G →* (Additive N ≃ₗ[ZMod p] Additive N) :=
    (automorphismLinear (N := N) (p := p)).comp φ
  have hρ : Function.Injective ρ :=
    (automorphismLinear_injective (N := N) (p := p)).comp hφ
  letI : Finite (Additive N ≃ₗ[ZMod p] Additive N) := Finite.of_injective
    (fun a : Additive N ≃ₗ[ZMod p] Additive N => (a : Additive N → Additive N))
    DFunLike.coe_injective
  exact CentralizerClassBound.class_card_le_of_injective ρ hρ 43904
    (FiniteBinaryFiveCentralizerRefinedBound.centralizer_card_le
      ((Nat.card_zmod p).trans hp) hN)

theorem class_card_le_sixtySevenEightThirtySeven (hp : p=2) (hN : Nat.card N=32)
    (φ : G →* MulAut N) (hφ : Function.Injective φ) :
    Nat.card (ConjClasses (N ⋊[φ] G)) ≤ 67837 := by
  letI : FiniteDimensional (ZMod p) (Additive N) := Module.Finite.of_finite
  let ρ : G →* (Additive N ≃ₗ[ZMod p] Additive N) :=
    (automorphismLinear (N := N) (p := p)).comp φ
  have hcompat (g : G) (n : N) : ρ g (Additive.ofMul n)=Additive.ofMul (φ g n) := rfl
  have hdual : Nat.card (Module.Dual (ZMod p) (Additive N))=32 := by
    calc
      _ = Nat.card (ZMod p)^Module.finrank (ZMod p)
          (Module.Dual (ZMod p) (Additive N)) := Module.natCard_eq_pow_finrank
      _ = Nat.card (ZMod p)^Module.finrank (ZMod p) (Additive N) := by
        rw [Subspace.dual_finrank_eq]
      _ = Nat.card N := (Module.natCard_eq_pow_finrank
        (K := ZMod p) (V := Additive N)).symm
      _ = 32 := hN
  have hs := AbelianSemidirectDualStabilizerClassBound.class_card_le_add_punctured_bound
    φ ρ hcompat 772 (BinaryFiveFunctionalStabilizerClassBound.class_card_le_sevenSeventyTwo
      hp hN φ hφ ρ hcompat)
  have ht := projected_class_card_le hp hN φ hφ
  rw [hdual] at hs
  omega

theorem subgroup_class_card_le_threeFiftyOneTwoForty (hp : p=2) (hN : Nat.card N=32)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] G)) : Nat.card (ConjClasses L) ≤ 351240 := by
  letI : Finite (N ⋊[φ] G) := Finite.of_equiv (N × G) SemidirectProduct.equivProd.symm
  let K := L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] G))
  by_cases hK : K=⊤
  · have hfull (n : N) : SemidirectProduct.inl n ∈ L := by
      have hn : n∈K := by rw [hK]; trivial
      exact hn
    let R := Projected φ L
    let ψ : R →* MulAut N := φ.comp R.subtype
    let e := overKernelEquiv φ L hfull
    letI : Finite (N ⋊[ψ] R) := Finite.of_equiv L e.toEquiv
    have hs := class_card_le_sixtySevenEightThirtySeven hp hN ψ
      (hφ.comp Subtype.val_injective)
    have hc : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses (N ⋊[ψ] R)) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    exact (hc.trans hs).trans (by decide)
  · let π : L →* G := (SemidirectProduct.rightHom : (N ⋊[φ] G) →* G).comp L.subtype
    let ψ : π.range →* MulAut N := φ.comp π.range.subtype
    have hψ : Function.Injective ψ := hφ.comp Subtype.val_injective
    by_cases hsmall : Nat.card K ≤ 8
    · have hk : Nat.card (ConjClasses π.ker) ≤ 8 :=
        (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
          ((AbelianSemidirectSubgroupCentralizerBound.kernel_card_le_intersection φ L).trans hsmall)
      have ht := projected_class_card_le hp hN ψ hψ
      exact (conjugacyClass_card_le_kernel_mul_range π).trans
        (by simpa using Nat.mul_le_mul hk ht)
    · have hle : Nat.card K ≤ 16 := BinarySmallElementSemidirectClassBound.proper_subgroup_card_le
        5 (by simpa using hN) K hK
      have hdiv : Nat.card K ∣ (2:ℕ)^5 := by
        simpa only [hN,show (2:ℕ)^5=32 by decide] using K.card_subgroup_dvd_card
      obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
      have hilow : 4 ≤ i := by
        by_contra h
        have hb : Nat.card K ≤ 8 := by
          rw [he]
          exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : i ≤ 3)
        exact hsmall hb
      have hiupper : i ≤ 4 := by
        by_contra h
        have hb : 32 ≤ Nat.card K := by
          rw [he]
          exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : 5 ≤ i)
        omega
      have hcardK : Nat.card K=16 := by
        rw [he,show i=4 by omega]
        decide
      have hindex : K.index=2 := by
        have hh := K.card_mul_index
        rw [hcardK,hN] at hh
        omega
      have hstable : ∀ (q : π.range) (n : N), ψ q n∈K ↔ n∈K :=
        AbelianSemidirectPlaneKernelClassBound.projected_preserves_intersection φ L
      have ht : Nat.card (ConjClasses π.range) ≤ 772 :=
        BinaryIndexTwoSixteenAutomorphismClassBound.class_card_le_sevenSeventyTwo
          hp K hcardK hindex ψ hψ hstable
      have hk : Nat.card (ConjClasses π.ker) ≤ 16 :=
        (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
          ((AbelianSemidirectSubgroupCentralizerBound.kernel_card_le_intersection φ L).trans_eq hcardK)
      exact ((conjugacyClass_card_le_kernel_mul_range π).trans
        (Nat.mul_le_mul hk ht)).trans (by decide)

end SymmetricSubgroupAsymptotics.BinaryThirtyTwoParabolicSubgroupClassBound
