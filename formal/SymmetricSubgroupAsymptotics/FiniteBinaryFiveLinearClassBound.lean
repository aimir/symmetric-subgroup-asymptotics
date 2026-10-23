import SymmetricSubgroupAsymptotics.FiniteBinaryFiveSpaceBounds
import SymmetricSubgroupAsymptotics.CentralizerClassBound

/-! Every actual faithful linear group on a 32-element binary space
has at most1015809 conjugacy classes. The estimate uses sparse
centralizer evaluations, not a list of linear subgroups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteBinaryFiveLinearClassBound

variable {K V H : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [Finite V] [Group H] [Finite H]

theorem class_card_le (hK : Nat.card K=2) (hV : Nat.card V=32)
    (ρ : H →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ) :
    Nat.card (ConjClasses H) ≤ 1015809 := by
  letI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun a : V ≃ₗ[K] V => (a : V → V)) DFunLike.coe_injective
  exact CentralizerClassBound.class_card_le_of_injective ρ hρ 1015808
    (FiniteBinaryFiveSpaceBounds.centralizer_card_le hK hV)

end SymmetricSubgroupAsymptotics.FiniteBinaryFiveLinearClassBound
