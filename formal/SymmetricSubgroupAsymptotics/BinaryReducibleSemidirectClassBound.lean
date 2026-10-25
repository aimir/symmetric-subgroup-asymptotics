import SymmetricSubgroupAsymptotics.BinaryReducibleLinearClassBound
import SymmetricSubgroupAsymptotics.AbelianActionClassBound

/-! The actual reducible projected group has at most five classes. The
original nonidentity translation fixed spaces have at most four points,
so the same-complement commuting-pair bound gives at most twenty-four
classes. The trivial complement is handled by its actual group order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryReducibleSemidirectClassBound

variable {K N G : Type} [Field K] [CommGroup N] [Group G]
    [Module K (Additive N)] [Finite K] [Finite N] [Finite G]

theorem class_card_le_twentyFour
    (hK : Nat.card K = 2) (hN : Nat.card N = 8)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n) = Additive.ofMul (φ g n))
    (W : Submodule K (Additive N)) (hWbot : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hstable : ∀ (g : G) (v : Additive N), v ∈ W → ρ g v ∈ W) :
    Nat.card (ConjClasses (N ⋊[φ] G)) ≤ 24 := by
  letI : Finite (N ⋊[φ] G) := Finite.of_equiv (N × G) SemidirectProduct.equivProd.symm
  letI : FiniteDimensional K (Additive N) := Module.Finite.of_finite
  have hρ : Function.Injective ρ := by
    intro g h he
    apply hφ
    apply MulEquiv.ext
    intro n
    have hn := DFunLike.congr_fun he (Additive.ofMul n)
    rw [hcompat, hcompat] at hn
    exact congrArg Additive.toMul hn
  have hA : Nat.card (Additive N) = 8 := hN
  have hd : Module.finrank K (Additive N) = 3 :=
    FiniteBinarySmallCentralizerBounds.finrank_eq_of_card_pow hK 3 (by simpa using hA)
  have htop : Nat.card (ConjClasses G) ≤ 5 :=
    BinaryReducibleLinearClassBound.class_card_le_five hK hA ρ hρ W hWbot hWtop hstable
  have hfixed (g : G) (hg : g ≠ 1) : Nat.card {n : N // φ g n = n} ≤ 4 := by
    have he : ρ g ≠ 1 := fun he => hg (hρ (he.trans ρ.map_one.symm))
    let e : {n : N // φ g n = n} ≃ {v : Additive N // ρ g v = v} := {
      toFun := fun n => ⟨Additive.ofMul n.val, by
        rw [hcompat]
        exact congrArg Additive.ofMul n.property⟩
      invFun := fun v => ⟨v.val.toMul, congrArg Additive.toMul
        ((hcompat g v.val.toMul).symm.trans v.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have hh := FiniteBinarySmallCentralizerBounds.fixed_card_le hK (ρ g) he
    exact (Nat.card_congr e).trans_le (by simpa only [hd] using hh)
  by_cases hone : Nat.card G = 1
  · have hc := Nat.card_le_card_of_surjective
      (@ConjClasses.mk (N ⋊[φ] G) _) ConjClasses.mk_surjective
    rw [SemidirectProduct.card, hN, hone, mul_one] at hc
    exact hc.trans (by decide)
  · have htwo : 2 ≤ Nat.card G := by
      have hp := Nat.card_pos (α := G)
      omega
    have hscale := AbelianActionClassBound.class_card_mul_complement_le φ 4 hfixed
    rw [hN] at hscale
    have height : 8 ≤ 4 * Nat.card G := by simpa using Nat.mul_le_mul_left 4 htwo
    have hbound : Nat.card G * Nat.card (ConjClasses (N ⋊[φ] G)) ≤ Nat.card G * 24 := by
      calc
        _ ≤ 8 + 4 * (Nat.card G * Nat.card (ConjClasses G)) := hscale
        _ ≤ 8 + 4 * (Nat.card G * 5) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ htop)) _
        _ ≤ 4 * Nat.card G + 4 * (Nat.card G * 5) := Nat.add_le_add_right height _
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hbound (Nat.card_pos (α := G))

end SymmetricSubgroupAsymptotics.BinaryReducibleSemidirectClassBound
