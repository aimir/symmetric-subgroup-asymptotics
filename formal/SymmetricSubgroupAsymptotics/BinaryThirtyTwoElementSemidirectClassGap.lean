import SymmetricSubgroupAsymptotics.FiniteBinaryFiveCentralizerRefinedBound
import SymmetricSubgroupAsymptotics.BinaryFiveElementSemidirectClassBound
import SymmetricSubgroupAsymptotics.AbelianSemidirectSubgroupCentralizerBound

/-! The actual five-dimensional binary translation module has a uniform
all-subgroup class bound with one extra GM power. The projected kernel
and complement remain those of the original subgroup throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryThirtyTwoElementSemidirectClassGap
open BinaryFiveElementSemidirectClassBound (automorphismLinear automorphismLinear_injective)

variable {N G : Type} [CommGroup N] [Group G] [Finite N] [Finite G]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive N)]

theorem subgroup_class_card_le (hp : p = 2) (hN : Nat.card N = 32)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] G)) : Nat.card (ConjClasses L) ≤ 702480 := by
  have hK : Nat.card (ZMod p) = 2 := (Nat.card_zmod p).trans hp
  have hA : Nat.card (Additive N) = 32 := hN
  let ρ : G →* (Additive N ≃ₗ[ZMod p] Additive N) :=
    (automorphismLinear (N := N) (p := p)).comp φ
  have hρ : Function.Injective ρ :=
    (automorphismLinear_injective (N := N) (p := p)).comp hφ
  letI : Finite (Additive N ≃ₗ[ZMod p] Additive N) :=
    Finite.of_injective (fun a : Additive N ≃ₗ[ZMod p] Additive N =>
      (a : Additive N → Additive N)) DFunLike.coe_injective
  have hfixed (g : G) (hg : g ≠ 1) : Nat.card {n : N // φ g n = n} ≤ 16 :=
    BinaryFiveElementSemidirectClassBound.fixed_card_le_sixteen hp hN φ hφ g hg
  have hcent (g : G) (hg : g ≠ 1) : Nat.card {a : G // Commute g a} ≤ 43904 :=
    AbelianActionCentralizerClassBound.centralizer_card_le_of_injective ρ hρ 43904
      (FiniteBinaryFiveCentralizerRefinedBound.centralizer_card_le hK hA) g hg
  have hproper (K : Subgroup N) (hK : K ≠ ⊤) : Nat.card K ≤ 16 :=
    BinaryFiveElementSemidirectClassBound.proper_subgroup_card_le_sixteen hN K hK
  have hcapacity : Nat.card N ≤ 16 * 43904 := by rw [hN]; decide
  simpa only [show 16 * (43904 + 1) = 702480 by decide] using
    AbelianSemidirectSubgroupCentralizerBound.subgroup_class_card_le
      φ 16 43904 hfixed hcent hproper hcapacity L

theorem subgroup_class_cube_gap (hp : p = 2) (hN : Nat.card N = 32)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] G)) :
    Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (Nat.card N - 2) := by
  calc
    Nat.card (ConjClasses L) ^ 3 ≤ 702480 ^ 3 :=
      Nat.pow_le_pow_left (subgroup_class_card_le hp hN φ hφ L) 3
    _ ≤ 5 ^ (Nat.card N - 2) := by rw [hN]; decide +kernel

end SymmetricSubgroupAsymptotics.BinaryThirtyTwoElementSemidirectClassGap
