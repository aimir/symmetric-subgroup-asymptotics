import SymmetricSubgroupAsymptotics.CFSGLinearBlockKernelOrderBudget
import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor
import SymmetricSubgroupAsymptotics.CFSGChiefPrimeFactorBudget

/-! Three reusable proper block dimensions in a six-dimensional binary
representation.  These bounds apply to the actual acting group and every
chosen original chief trace; they do not assert that a block chart exists. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGLinearBlockOrderSelected
open CFSGLinearBlockKernelOrderBudget CFSGChiefPrimeFactorBudget

theorem binary_linearEquiv_card (d : ℕ) :
    Nat.card ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) =
      fullLinearOrder 2 d := by
  let e := (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun (ZMod 2) (Fin d))).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin d → ZMod 2))
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp only [fullLinearOrder, ZMod.card]

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

theorem binary_block_order_dvd {b d : ℕ}
    (rho : Representation (ZMod 2) G V) (hfaithful : Function.Injective rho)
    (e : V ≃ₗ[ZMod 2] (Fin b → Fin d → ZMod 2))
    (pi : G →* Equiv.Perm (Fin b))
    (hker : ∀ (g : pi.ker) (v : V) (i : Fin b),
      e v i = 0 → e (rho g.val v) i = 0) :
    Nat.card G ∣ (fullLinearOrder 2 d) ^ b * Nat.factorial b := by
  simpa only [binary_linearEquiv_card, Fintype.card_fin] using
    card_dvd_of_block_chart rho hfaithful e pi hker

theorem selected_block_omega :
    ArithmeticFunction.cardFactors ((fullLinearOrder 2 3)^2 * Nat.factorial 2) = 11 ∧
    ArithmeticFunction.cardFactors ((fullLinearOrder 2 2)^3 * Nat.factorial 3) = 8 ∧
    ArithmeticFunction.cardFactors ((fullLinearOrder 2 1)^6 * Nat.factorial 6) = 7 := by
  unfold fullLinearOrder
  decide +kernel

/-- Every proper homogeneous block count dividing six fits the required
fourteen-unit trace budget, with room to spare. -/
theorem trace_le_fourteen_of_binary_block_chart {b d : ℕ}
    (hbd : (b = 2 ∧ d = 3) ∨ (b = 3 ∧ d = 2) ∨ (b = 6 ∧ d = 1))
    (rho : Representation (ZMod 2) G V) (hfaithful : Function.Injective rho)
    (e : V ≃ₗ[ZMod 2] (Fin b → Fin d → ZMod 2))
    (pi : G →* Equiv.Perm (Fin b))
    (hker : ∀ (g : pi.ker) (v : V) (i : Fin b),
      e v i = 0 → e (rho g.val v) i = 0)
    (T : FixedTargetCompositionTrace G) : T.envelope.abelianLength ≤ 14 := by
  have hdiv := binary_block_order_dvd rho hfaithful e pi hker
  have hne : (fullLinearOrder 2 d)^b * Nat.factorial b ≠ 0 := by
    rcases hbd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  have htrace := (trace_charge_le_cardFactors T).trans
    (cardFactors_mono hne hdiv)
  rcases hbd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [selected_block_omega.1] at htrace
    omega
  · rw [selected_block_omega.2.1] at htrace
    omega
  · rw [selected_block_omega.2.2] at htrace
    omega

end SymmetricSubgroupAsymptotics.CFSGLinearBlockOrderSelected
