import SymmetricSubgroupAsymptotics.LinearSemidirectInertiaClassCardinality
import SymmetricSubgroupAsymptotics.AffineStabilizerClassDomination
import SymmetricSubgroupAsymptotics.BilinearContragredientDuality

/-! A preserved nondegenerate pairing transfers genuine natural
nonzero transitivity to the dual. The exact semidirect/inertia identity
then bounds the affine class number by the classes of the SAME group
and its SAME actual nonzero-vector stabilizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.LinearSemidirectTwoOrbitClassBound
open LinearSemidirectCommutingFibres GroupActionInertia
open BilinearContragredientDuality AffineStabilizerClassDomination

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

theorem class_card_le [Finite G] [Finite K] [Module.Finite K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (ρ : G →* (V ≃ₗ[K] V))
    (hρ : ∀ g : G, ∀ x y : V, B (ρ g x) (ρ g y) = B x y)
    (v : V) (hv : v ≠ 0)
    (htrans : ∀ x y : V, x ≠ 0 → y ≠ 0 → ∃ g : G, ρ g x = y) :
    letI := naturalAction ρ
    Nat.card (ConjClasses (AffineGroup ρ)) ≤
      Nat.card (ConjClasses G) + Nat.card (ConjClasses (MulAction.stabilizer G v)) := by
  letI := naturalAction ρ
  letI := BinaryQuadraticRefinementAction.dualAction ρ
  let φ := B.toDual hB v
  have hφ : φ ≠ 0 := by
    intro he
    apply hv
    apply (B.toDual hB).injective
    exact he.trans (map_zero (B.toDual hB)).symm
  have ht : ∀ ψ : Module.Dual K V, ψ ≠ 0 → ∃ g : G, g • φ = ψ := by
    intro ψ hψ
    exact dual_nonzero_transitive B hB ρ hρ htrans φ ψ hφ hψ
  have hc := linear_inertia_card_le φ ht
  have hs : MulAction.stabilizer G φ = MulAction.stabilizer G v :=
    stabilizer_toDual_eq B hB ρ hρ v
  rw [hs] at hc
  exact (LinearSemidirectInertiaClassCardinality.class_card_eq_dual_inertia ρ).le.trans hc

end SymmetricSubgroupAsymptotics.LinearSemidirectTwoOrbitClassBound
