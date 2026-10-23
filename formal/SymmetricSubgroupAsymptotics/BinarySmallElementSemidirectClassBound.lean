import SymmetricSubgroupAsymptotics.FiniteBinarySmallCentralizerBounds
import SymmetricSubgroupAsymptotics.AbelianSemidirectSubgroupCentralizerBound
import SymmetricSubgroupAsymptotics.BinaryFiveElementSemidirectClassBound

/-! All subgroups of actual elementary binary semidirect products
of translation orders8 and16 have at most36 and2312 classes. Every
linear fixed-space and centralizer capacity is proved internally. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySmallElementSemidirectClassBound
open BinaryFiveElementSemidirectClassBound (automorphismLinear automorphismLinear_injective)

variable {N H : Type*} [CommGroup N] [Group H] [Finite N] [Finite H]

theorem proper_subgroup_card_le (a : ℕ) (hN : Nat.card N=2^a)
    (K : Subgroup N) (hK : K ≠ ⊤) : Nat.card K ≤ 2^(a-1) := by
  have hd : Nat.card K ∣ (2 : ℕ)^a := by
    simpa only [hN] using K.card_subgroup_dvd_card
  obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hia : i < a := by
    by_contra hn
    have heq : i=a := by omega
    apply hK
    apply K.eq_top_of_card_eq
    exact he.trans (by rw [heq]; exact hN.symm)
  calc
    Nat.card K = 2^i := he
    _ ≤ 2^(a-1) := Nat.pow_le_pow_right (by decide) (by omega)

variable {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive N)]

private theorem subgroup_class_card_le_of_linear_bounds
    (φ : H →* MulAut N) (hφ : Function.Injective φ) (d c : ℕ)
    (hfixed : ∀e : Additive N ≃ₗ[ZMod p] Additive N, e ≠ 1 →
      Nat.card {v : Additive N // e v=v} ≤ d)
    (hcent : ∀e : Additive N ≃ₗ[ZMod p] Additive N, e ≠ 1 →
      Nat.card {a : Additive N ≃ₗ[ZMod p] Additive N // Commute e a} ≤ c)
    (hproper : ∀K : Subgroup N, K ≠ ⊤ → Nat.card K ≤ d)
    (hcapacity : Nat.card N ≤ d*c) (L : Subgroup (N ⋊[φ] H)) :
    Nat.card (ConjClasses L) ≤ d*(c+1) := by
  let ρ : H →* (Additive N ≃ₗ[ZMod p] Additive N) :=
    (automorphismLinear (N := N) (p := p)).comp φ
  have hρ : Function.Injective ρ :=
    (automorphismLinear_injective (N := N) (p := p)).comp hφ
  letI : Finite (Additive N ≃ₗ[ZMod p] Additive N) :=
    Finite.of_injective (fun a : Additive N ≃ₗ[ZMod p] Additive N =>
      (a : Additive N → Additive N)) DFunLike.coe_injective
  have hfixedH (h : H) (hh : h ≠ 1) : Nat.card {n : N // φ h n=n} ≤ d := by
    have he : ρ h ≠ 1 := fun he => hh (hρ (he.trans ρ.map_one.symm))
    let e : {n : N // φ h n=n} ≃ {v : Additive N // ρ h v=v} := {
      toFun := fun n => ⟨Additive.ofMul n.val,congrArg Additive.ofMul n.property⟩
      invFun := fun v => ⟨v.val.toMul,congrArg Additive.toMul v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans_le (hfixed (ρ h) he)
  have hcentH (h : H) (hh : h ≠ 1) : Nat.card {k : H // Commute h k} ≤ c :=
    AbelianActionCentralizerClassBound.centralizer_card_le_of_injective ρ hρ c hcent h hh
  exact AbelianSemidirectSubgroupCentralizerBound.subgroup_class_card_le
    φ d c hfixedH hcentH hproper hcapacity L

theorem subgroup_class_card_le_thirtySix
    (hp : p=2) (hN : Nat.card N=8)
    (φ : H →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] H)) : Nat.card (ConjClasses L) ≤ 36 := by
  have hK : Nat.card (ZMod p)=2 := (Nat.card_zmod p).trans hp
  have hA : Nat.card (Additive N)=8 := hN
  have hd : Module.finrank (ZMod p) (Additive N)=3 :=
    FiniteBinarySmallCentralizerBounds.finrank_eq_of_card_pow
      (K := ZMod p) (V := Additive N) hK 3 (by simpa using hA)
  apply subgroup_class_card_le_of_linear_bounds (p := p) φ hφ 4 8
  · intro e he
    have hh := FiniteBinarySmallCentralizerBounds.fixed_card_le hK e he
    simpa only [hd] using hh
  · exact FiniteBinarySmallCentralizerBounds.centralizer_card_le_eight hK hA
  · intro K hK
    exact proper_subgroup_card_le 3 (by simpa using hN) K hK
  · rw [hN]
    decide

theorem subgroup_class_card_le_twoThousandThreeTwelve
    (hp : p=2) (hN : Nat.card N=16)
    (φ : H →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] H)) : Nat.card (ConjClasses L) ≤ 2312 := by
  have hK : Nat.card (ZMod p)=2 := (Nat.card_zmod p).trans hp
  have hA : Nat.card (Additive N)=16 := hN
  have hd : Module.finrank (ZMod p) (Additive N)=4 :=
    FiniteBinarySmallCentralizerBounds.finrank_eq_of_card_pow
      (K := ZMod p) (V := Additive N) hK 4 (by simpa using hA)
  apply subgroup_class_card_le_of_linear_bounds (p := p) φ hφ 8 288
  · intro e he
    have hh := FiniteBinarySmallCentralizerBounds.fixed_card_le hK e he
    simpa only [hd] using hh
  · exact FiniteBinarySmallCentralizerBounds.centralizer_card_le_twoEightyEight hK hA
  · intro K hK
    exact proper_subgroup_card_le 4 (by simpa using hN) K hK
  · rw [hN]
    decide

end SymmetricSubgroupAsymptotics.BinarySmallElementSemidirectClassBound
