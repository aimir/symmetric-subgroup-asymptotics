import SymmetricSubgroupAsymptotics.LinearInvariantPlaneComplementClassBound
import SymmetricSubgroupAsymptotics.LinearContragredientSmallSpaceAction
import SymmetricSubgroupAsymptotics.FiniteBinarySmallCentralizerBounds

/-! A faithful reducible action on a binary space of order eight has at
most five classes. An invariant plane gives the literal complement
action. An invariant line gives an actual invariant annihilator plane
for the faithful contragredient action of the SAME group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryReducibleLinearClassBound
open LinearContragredientSmallSpaceAction

variable {K V G : Type} [Field K] [AddCommGroup V] [Module K V] [Group G]

theorem annihilator_stable (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hstable : ∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W)
    (g : G) (ℓ : Module.Dual K V) (hℓ : ℓ ∈ W.dualAnnihilator) :
    contragredient ρ g ℓ ∈ W.dualAnnihilator := by
  apply (W.mem_dualAnnihilator _).mpr
  intro v hv
  change ℓ ((ρ g).symm v) = 0
  have hinv : ρ g⁻¹ = (ρ g).symm := by rw [ρ.map_inv]; rfl
  have hmem : (ρ g).symm v ∈ W := by
    rw [← hinv]
    exact hstable g⁻¹ v hv
  exact (W.mem_dualAnnihilator ℓ).mp hℓ _ hmem

theorem class_card_le_five [Finite K] [Finite V] [Finite G]
    (hK : Nat.card K = 2) (hV : Nat.card V = 8)
    (ρ : G →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ)
    (W : Submodule K V) (hWbot : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hstable : ∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) :
    Nat.card (ConjClasses G) ≤ 5 := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  letI : Finite (Module.Dual K V) := Finite.of_injective
    (fun ℓ : Module.Dual K V => (ℓ : V → K)) DFunLike.coe_injective
  have hd : Module.finrank K V = 3 :=
    FiniteBinarySmallCentralizerBounds.finrank_eq_of_card_pow hK 3 (by simpa using hV)
  have hpos : 0 < Module.finrank K W := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hWbot (Submodule.finrank_eq_zero.mp hz)
  have hlt := Submodule.finrank_lt hWtop
  have hdim : Module.finrank K W = 1 ∨ Module.finrank K W = 2 := by omega
  rcases hdim with hone | htwo
  · have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    have hAnnDim : Module.finrank K W.dualAnnihilator = 2 := by omega
    have hAnnCard : Nat.card W.dualAnnihilator = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := W.dualAnnihilator), hK, hAnnDim]
      decide
    have hDualCard : Nat.card (Module.Dual K V) = 8 := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := Module.Dual K V),
        Subspace.dual_finrank_eq, hK, hd]
      decide
    exact LinearInvariantPlaneComplementClassBound.class_card_le_five hDualCard
      (contragredient ρ) (contragredient_injective ρ hρ)
      W.dualAnnihilator hAnnCard (annihilator_stable ρ W hstable)
  · have hWCard : Nat.card W = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := W), hK, htwo]
      decide
    exact LinearInvariantPlaneComplementClassBound.class_card_le_five hV ρ hρ W hWCard hstable

end SymmetricSubgroupAsymptotics.BinaryReducibleLinearClassBound
