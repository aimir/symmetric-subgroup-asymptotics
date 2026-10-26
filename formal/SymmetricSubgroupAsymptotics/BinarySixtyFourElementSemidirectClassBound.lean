import SymmetricSubgroupAsymptotics.FiniteBinarySparseCentralizerBound
import SymmetricSubgroupAsymptotics.BinarySmallElementSemidirectClassBound

/-! The generic sparse centralizer chart suffices for64 translations.
Fixed and proper kernel spaces have at most32 elements; all bounds are
pulled through the same actual faithful complement and original subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySixtyFourElementSemidirectClassBound
open BinaryFiveElementSemidirectClassBound (automorphismLinear automorphismLinear_injective)

def classBudget : ℕ := 32*(2^30+1)

variable {N G : Type} [CommGroup N] [Group G] [Finite N] [Finite G]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive N)]

theorem subgroup_class_card_le (hp : p=2) (hN : Nat.card N=64)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] G)) : Nat.card (ConjClasses L) ≤ classBudget := by
  have hK : Nat.card (ZMod p)=2 := (Nat.card_zmod p).trans hp
  have hA : Nat.card (Additive N)=64 := hN
  letI : Nontrivial (Additive N) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hd : Module.finrank (ZMod p) (Additive N)=6 :=
    FiniteBinarySmallCentralizerBounds.finrank_eq_of_card_pow hK 6 (by simpa using hA)
  let ρ : G →* (Additive N ≃ₗ[ZMod p] Additive N) :=
    (automorphismLinear (N := N) (p := p)).comp φ
  have hρ : Function.Injective ρ :=
    (automorphismLinear_injective (N := N) (p := p)).comp hφ
  letI : Finite (Additive N ≃ₗ[ZMod p] Additive N) := Finite.of_injective
    (fun a : Additive N ≃ₗ[ZMod p] Additive N => (a : Additive N → Additive N))
    DFunLike.coe_injective
  have hfixed (g : G) (hg : g≠1) : Nat.card {n : N // φ g n=n} ≤ 32 := by
    have he : ρ g≠1 := fun he => hg (hρ (he.trans ρ.map_one.symm))
    let e : {n : N // φ g n=n} ≃ {v : Additive N // ρ g v=v} := {
      toFun := fun n => ⟨Additive.ofMul n.val,congrArg Additive.ofMul n.property⟩
      invFun := fun v => ⟨v.val.toMul,congrArg Additive.toMul v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans_le (by
      simpa only [hd] using FiniteBinarySmallCentralizerBounds.fixed_card_le hK (ρ g) he)
  have hc (e : Additive N ≃ₗ[ZMod p] Additive N) (he : e≠1) :
      Nat.card {a : Additive N ≃ₗ[ZMod p] Additive N // Commute e a} ≤ 2^30 := by
    have hh := FiniteBinarySparseCentralizerBound.centralizer_card_le hK e he
    rw [hA,hd] at hh
    exact hh.trans (by decide +kernel)
  have hcent (g : G) (hg : g≠1) : Nat.card {a : G // Commute g a} ≤ 2^30 :=
    AbelianActionCentralizerClassBound.centralizer_card_le_of_injective ρ hρ (2^30) hc g hg
  have hproper (K : Subgroup N) (hK : K≠⊤) : Nat.card K ≤ 32 :=
    BinarySmallElementSemidirectClassBound.proper_subgroup_card_le
      6 (by simpa using hN) K hK
  have hcapacity : Nat.card N ≤ 32*2^30 := by rw [hN]; decide
  exact AbelianSemidirectSubgroupCentralizerBound.subgroup_class_card_le
    φ 32 (2^30) hfixed hcent hproper hcapacity L

end SymmetricSubgroupAsymptotics.BinarySixtyFourElementSemidirectClassBound
