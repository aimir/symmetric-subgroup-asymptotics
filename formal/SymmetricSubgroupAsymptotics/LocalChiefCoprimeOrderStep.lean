import SymmetricSubgroupAsymptotics.LocalChiefQuotientCoordinates
import SymmetricSubgroupAsymptotics.ChiefTernaryFiltration

/-! An actual local factor of order prime to three contributes no
ternary head. The actual source section embeds by the literal conjugate
coordinates; its exponent divides the original local factor order.
No identification of another prime, or assumption on action order, is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A R : Type} [Group A] [Group R] [Finite R]
variable (N H : Subgroup A) [N.Normal] (θ : N→*R)
variable (B L : Subgroup R) [B.Normal] [L.Normal]

theorem actualChiefIntersection_local_order_exponent
    (x:localChiefSourceSection N θ B L) :
    x^(Nat.card (normalChainQuotient B L))=1 := by
  apply localChiefQuotientCoordinates_separate N θ B L
  funext a
  simp only [map_pow,map_one]
  exact pow_card_eq_one'

theorem actualCoprimeOrderChiefIntersectionStep [Finite A] (hBL:B≤L)
    (hc : (Nat.card (normalChainQuotient B L):ZMod 3)≠0) :
    TernaryChiefStep (localChiefIntersection N θ B) (localChiefIntersection N θ L) H 0 := by
  apply TernaryChiefStep.coprime (localChiefIntersection_mono N θ hBL)
    (Nat.card (normalChainQuotient B L)) hc
  intro x
  refine ⟨1,?_⟩
  rw [pow_one]
  exact actualChiefIntersection_local_order_exponent N θ B L x

end SymmetricSubgroupAsymptotics
