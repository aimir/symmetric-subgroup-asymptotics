import SymmetricSubgroupAsymptotics.AbelianSemidirectPuncturedClassIdentity
import SymmetricSubgroupAsymptotics.BinaryFunctionalStabilizerClassBound
import SymmetricSubgroupAsymptotics.FiniteBinarySmallCentralizerBounds
import SymmetricSubgroupAsymptotics.CentralizerClassBound

/-! A faithful irreducible binary action on an actual translation group
of order eight gives at most fourteen semidirect-product classes. Both
summands are proved: the original projected group has at most nine
classes and its actual nonzero functional stabilizer has at most five.
No subgroup census, self-duality or desired capacity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryIrreducibleSemidirectClassBound
open LinearContragredientSmallSpaceAction AbelianSemidirectPuncturedClassIdentity

variable {K : Type*} {N G : Type} [Field K] [CommGroup N] [Group G]
    [Module K (Additive N)] [Finite K] [Finite N] [Finite G]

theorem class_card_le_fourteen
    (hK : Nat.card K = 2) (hN : Nat.card N = 8)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n) = Additive.ofMul (φ g n))
    (hirr : ∀ W : Submodule K (Additive N),
      (∀ (g : G) (v : Additive N), v ∈ W → ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) :
    Nat.card (ConjClasses (N ⋊[φ] G)) ≤ 14 := by
  letI : FiniteDimensional K (Additive N) := Module.Finite.of_finite
  letI : Finite (Additive N ≃ₗ[K] Additive N) := Finite.of_injective
    (fun e : Additive N ≃ₗ[K] Additive N => (e : Additive N → Additive N))
    DFunLike.coe_injective
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
  have htop : Nat.card (ConjClasses G) ≤ 9 :=
    CentralizerClassBound.class_card_le_of_injective ρ hρ 8
      (FiniteBinarySmallCentralizerBounds.centralizer_card_le_eight hK hA)
  have hdDual : Module.finrank K (Module.Dual K (Additive N)) = 3 := by
    rw [Subspace.dual_finrank_eq, hd]
  letI : Nontrivial (Module.Dual K (Additive N)) :=
    Module.nontrivial_of_finrank_pos (by rw [hdDual]; decide)
  obtain ⟨ℓ, hℓ⟩ := exists_ne (0 : Module.Dual K (Additive N))
  have htrans (f g : Module.Dual K (Additive N)) (hf : f ≠ 0) (hg : g ≠ 0) :
      ∃ a : G, contragredient ρ a f = g := by
    apply exists_dual_map_eq_of_nonzero ρ hirr
    · rw [hd]
      decide
    · rw [hA, hd]
    · exact hf
    · exact hg
  have hsplit : Nat.card (ConjClasses (N ⋊[φ] G)) = Nat.card (ConjClasses G) +
      Nat.card (ConjClasses (AbelianSemidirectDualClassIdentity.dualStabilizer ρ ℓ)) :=
    class_card_eq_add_dual_stabilizer φ ρ hcompat htrans ⟨ℓ, hℓ⟩
  have hstab := BinaryFunctionalStabilizerClassBound.class_card_le_five
    hK hN φ hφ ρ hcompat ℓ hℓ
  rw [hsplit]
  omega

end SymmetricSubgroupAsymptotics.BinaryIrreducibleSemidirectClassBound
