import SymmetricSubgroupAsymptotics.FiniteBinaryFourCentralizerSharpBound
import SymmetricSubgroupAsymptotics.BinarySmallElementSemidirectClassBound

/-! The sharp actual linear centralizer bound192 gives an all-subgroup
bound1544 for a faithful elementary binary semidirect product with16
translations. This is an original subgroup bound: fixed spaces and
centralizers are pulled back through its actual faithful complement,
with no class monotonicity or splitting assumption on the subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySixteenElementSemidirectClassGap
open BinaryFiveElementSemidirectClassBound (automorphismLinear automorphismLinear_injective)

variable {N G : Type} [CommGroup N] [Group G] [Finite N] [Finite G]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive N)]

theorem subgroup_class_card_le_fifteenFortyFour
    (hp : p=2) (hN : Nat.card N=16)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] G)) : Nat.card (ConjClasses L) ≤ 1544 := by
  have hK : Nat.card (ZMod p)=2 := (Nat.card_zmod p).trans hp
  have hA : Nat.card (Additive N)=16 := hN
  have hd : Module.finrank (ZMod p) (Additive N)=4 :=
    FiniteBinarySmallCentralizerBounds.finrank_eq_of_card_pow
      (K := ZMod p) (V := Additive N) hK 4 (by simpa using hA)
  let ρ : G →* (Additive N ≃ₗ[ZMod p] Additive N) :=
    (automorphismLinear (N := N) (p := p)).comp φ
  have hρ : Function.Injective ρ :=
    (automorphismLinear_injective (N := N) (p := p)).comp hφ
  letI : Finite (Additive N ≃ₗ[ZMod p] Additive N) :=
    Finite.of_injective (fun a : Additive N ≃ₗ[ZMod p] Additive N =>
      (a : Additive N → Additive N)) DFunLike.coe_injective
  have hfixed (g : G) (hg : g ≠ 1) : Nat.card {n : N // φ g n=n} ≤ 8 := by
    have he : ρ g ≠ 1 := fun he => hg (hρ (he.trans ρ.map_one.symm))
    let e : {n : N // φ g n=n} ≃ {v : Additive N // ρ g v=v} := {
      toFun := fun n => ⟨Additive.ofMul n.val,congrArg Additive.ofMul n.property⟩
      invFun := fun v => ⟨v.val.toMul,congrArg Additive.toMul v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans_le (by
      simpa only [hd] using FiniteBinarySmallCentralizerBounds.fixed_card_le hK (ρ g) he)
  have hcent (g : G) (hg : g ≠ 1) : Nat.card {a : G // Commute g a} ≤ 192 :=
    AbelianActionCentralizerClassBound.centralizer_card_le_of_injective ρ hρ 192
      (FiniteBinaryFourCentralizerSharpBound.centralizer_card_le_oneNinetyTwo hK hA) g hg
  have hproper (K : Subgroup N) (hK : K ≠ ⊤) : Nat.card K ≤ 8 :=
    BinarySmallElementSemidirectClassBound.proper_subgroup_card_le
      4 (by simpa using hN) K hK
  have hcapacity : Nat.card N ≤ 8*192 := by rw [hN]; decide
  simpa only [show 8*(192+1)=1544 by decide] using
    AbelianSemidirectSubgroupCentralizerBound.subgroup_class_card_le
      φ 8 192 hfixed hcent hproper hcapacity L

theorem subgroup_class_cube_gap
    (hp : p=2) (hN : Nat.card N=16)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] G)) :
    Nat.card (ConjClasses L)^3 ≤ 5^(Nat.card N-2) := by
  calc
    Nat.card (ConjClasses L)^3 ≤ 1544^3 :=
      Nat.pow_le_pow_left (subgroup_class_card_le_fifteenFortyFour hp hN φ hφ L) 3
    _ ≤ 5^(Nat.card N-2) := by rw [hN]; decide +kernel

end SymmetricSubgroupAsymptotics.BinarySixteenElementSemidirectClassGap
