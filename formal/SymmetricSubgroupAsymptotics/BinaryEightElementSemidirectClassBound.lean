import SymmetricSubgroupAsymptotics.BinaryIrreducibleSemidirectClassBound
import SymmetricSubgroupAsymptotics.BinaryReducibleSemidirectClassBound
import SymmetricSubgroupAsymptotics.BinaryProperIntersectionSemidirectClassBound

/-! Every actual subgroup of a faithful binary affine semidirect product
with eight translations has at most twenty-four classes. The literal
translation intersection is trivial, nonzero proper, or full. In the
full case the subgroup is identified with its OWN projected semidirect
product, whose action is genuinely irreducible or genuinely reducible.
No ambient subgroup-class monotonicity or action census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryEightElementSemidirectClassBound
open BinaryFiveElementSemidirectClassBound (automorphismLinear automorphismLinear_injective)
open SemidirectSubgroupOverKernel

variable {N G : Type} [CommGroup N] [Group G] [Finite N] [Finite G]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive N)]

theorem subgroup_class_card_le_twentyFour (hp : p = 2) (hN : Nat.card N = 8)
    (φ : G →* MulAut N) (hφ : Function.Injective φ) (L : Subgroup (N ⋊[φ] G)) :
    Nat.card (ConjClasses L) ≤ 24 := by
  letI : Finite (N ⋊[φ] G) := Finite.of_equiv (N × G) SemidirectProduct.equivProd.symm
  let K := L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] G))
  have hK : Nat.card (ZMod p) = 2 := (Nat.card_zmod p).trans hp
  have hA : Nat.card (Additive N) = 8 := hN
  by_cases hbot : K = ⊥
  · let π : L →* G := (SemidirectProduct.rightHom : (N ⋊[φ] G) →* G).comp L.subtype
    let ρ : G →* (Additive N ≃ₗ[ZMod p] Additive N) :=
      (automorphismLinear (N := N) (p := p)).comp φ
    letI : Finite (Additive N ≃ₗ[ZMod p] Additive N) := Finite.of_injective
      (fun e : Additive N ≃ₗ[ZMod p] Additive N => (e : Additive N → Additive N))
      DFunLike.coe_injective
    have hπ : Function.Injective π := rightHom_injective_of_comap_bot φ L hbot
    have hρ : Function.Injective ρ :=
      (automorphismLinear_injective (N := N) (p := p)).comp hφ
    have hc : Nat.card (ConjClasses L) ≤ 9 :=
      CentralizerClassBound.class_card_le_of_injective (ρ.comp π) (hρ.comp hπ) 8
        (FiniteBinarySmallCentralizerBounds.centralizer_card_le_eight hK hA)
    exact hc.trans (by decide)
  · by_cases htop : K = ⊤
    · have hfull (n : N) : SemidirectProduct.inl n ∈ L := by
        have hn : n ∈ K := by rw [htop]; trivial
        exact hn
      let R := Projected φ L
      let ψ : R →* MulAut N := φ.comp R.subtype
      let σ : R →* (Additive N ≃ₗ[ZMod p] Additive N) :=
        (automorphismLinear (N := N) (p := p)).comp ψ
      let e := overKernelEquiv φ L hfull
      letI : Finite (N ⋊[ψ] R) := Finite.of_equiv L e.toEquiv
      have hψ : Function.Injective ψ := hφ.comp Subtype.val_injective
      have hcompat (r : R) (n : N) : σ r (Additive.ofMul n) = Additive.ofMul (ψ r n) := rfl
      have htransfer : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses (N ⋊[ψ] R)) :=
        Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
          (ConjClasses.map_surjective e.symm.surjective)
      apply htransfer.trans
      by_cases hirr : ∀ W : Submodule (ZMod p) (Additive N),
          (∀ (r : R) (v : Additive N), v ∈ W → σ r v ∈ W) → W = ⊥ ∨ W = ⊤
      · exact (BinaryIrreducibleSemidirectClassBound.class_card_le_fourteen
          hK hN ψ hψ σ hcompat hirr).trans (by decide)
      · have hred : ∃ W : Submodule (ZMod p) (Additive N),
            (∀ (r : R) (v : Additive N), v ∈ W → σ r v ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
          by_contra hno
          apply hirr
          intro W hstable
          by_cases hb : W = ⊥
          · exact Or.inl hb
          · right
            by_contra ht
            exact hno ⟨W, hstable, hb, ht⟩
        obtain ⟨W, hstable, hb, ht⟩ := hred
        exact BinaryReducibleSemidirectClassBound.class_card_le_twentyFour
          hK hN ψ hψ σ hcompat W hb ht hstable
    · exact (BinaryProperIntersectionSemidirectClassBound.class_card_le_twenty
        hp hN φ hφ L hbot htop).trans (by decide)

end SymmetricSubgroupAsymptotics.BinaryEightElementSemidirectClassBound
