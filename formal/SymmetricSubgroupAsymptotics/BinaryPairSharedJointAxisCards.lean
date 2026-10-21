import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds
import SymmetricSubgroupAsymptotics.BinaryPairSharedBinding

/-! Exact transports of the three joint axis factors through the retained
top equivalence. The axis is always the literal original normal's axis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X H : Type} [Finite X] [Group H] [Finite H] {w : ℕ}
    {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin w))
    (rho : Representation (ZMod 2) H (Fin w → ZMod 2))
    (e : H ≃* F.top.range)
    (he : ∀ g v, rho g v = F.coordinateTopAction (e g) v)
include e he
omit [Finite X] [Finite H]

theorem shared_fixed_axis_card (N : Subgroup U) (K : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hK : K = F.kernelSpace) :
    Nat.card {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
      ∀ t : F.top.range, F.coordinateTopAction t v - v ∈ F.ambientAxis N} =
    Nat.card {v : Fin w → ZMod 2 // v ∈ K ∧
      ∀ t : H, rho t v - v ∈ F.ambientAxis N} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro v
  rw [hK]
  apply and_congr_right
  intro _
  constructor
  · intro h t
    rw [he]
    exact h (e t)
  · intro h t
    obtain ⟨g, rfl⟩ := e.surjective t
    rw [← he]
    exact h g

theorem shared_top_axis_card (N : Subgroup U) (K : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hK : K = F.kernelSpace) :
    Nat.card {t : F.top.range // ∀ v, v ∈ F.kernelSpace →
      F.coordinateTopAction t v - v ∈ F.ambientAxis N} =
    Nat.card {t : H // ∀ v, v ∈ K → rho t v - v ∈ F.ambientAxis N} := by
  symm
  apply Nat.card_congr
  refine e.toEquiv.subtypeEquiv ?_
  intro t
  simp only [hK, he]
  rfl

theorem shared_central_top_axis_card (N : Subgroup U)
    (K : Submodule (ZMod 2) (Fin w → ZMod 2)) (hK : K = F.kernelSpace) :
    Nat.card {t : F.top.range // t ∈ Subgroup.center F.top.range ∧
      ∀ v, v ∈ F.kernelSpace → F.coordinateTopAction t v - v ∈ F.ambientAxis N} =
    Nat.card {t : H // t ∈ Subgroup.center H ∧
      ∀ v, v ∈ K → rho t v - v ∈ F.ambientAxis N} := by
  symm
  apply Nat.card_congr
  refine e.toEquiv.subtypeEquiv ?_
  intro t
  have hc : t ∈ Subgroup.center H ↔ e t ∈ Subgroup.center F.top.range := by
    rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro h s
      obtain ⟨g, rfl⟩ := e.surjective s
      simpa only [map_mul] using congrArg e (h g)
    · intro h g
      apply e.injective
      simpa only [map_mul] using h (e g)
  simp only [hK, he, hc]
  rfl

end SymmetricSubgroupAsymptotics.BinaryPairFrame
