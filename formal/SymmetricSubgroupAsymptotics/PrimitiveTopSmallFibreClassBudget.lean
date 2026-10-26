import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedGeneralClassReserve
import SymmetricSubgroupAsymptotics.QuasiprimitiveSwapRecognition
import SymmetricSubgroupAsymptotics.SubnormalSmallFibreTopClassBound
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction

/-! A common native consumer for binary and ternary fibres. The actual
primitive top has a proved subnormal-class budget and order below the
full symmetric group. The binary branch keeps the unsigned motion
reserve; the ternary branch uses the actual projected class budget.
Every numerical hypothesis is an explicit scalar inequality, to be
discharged by the selected concrete degree instance. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveTopSmallFibreClassBudget
open OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_le_at_original_degree
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω) = g • π ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x) = c)
    (hn : 2 ≤ Nat.card X)
    (hprimitive : MulAction.IsPreprimitive (Top (A := A) (X := X)) X)
    (horder : Nat.card (Top (A := A) (X := X)) < (Nat.card X).factorial)
    (B : ℕ) (hB : 11 ≤ B)
    (htop : ∀ L : Subgroup (Top (A := A) (X := X)), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤ B)
    (hbinary : ((B + 1) * 2 ^ (Nat.card X - 2)) ^ 3 ≤ 5 ^ (2 * Nat.card X - 1))
    (hternary : (3 ^ Nat.card X * B) ^ 3 ≤ 5 ^ (3 * Nat.card X - 1))
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  rcases hc with rfl | rfl
  · letI : Fintype X := Fintype.ofFinite X
    letI : DecidableEq X := Classical.decEq X
    letI : MulAction.IsPreprimitive (Top (A := A) (X := X)) X := hprimitive
    have hns : ∀ a : A, ¬ (topMap (A := A) (X := X) a).IsSwap := by
      intro a ha
      have ht : Top (A := A) (X := X) = ⊤ :=
        QuasiprimitiveSwapRecognition.eq_top_of_isSwap_mem
          (Top (A := A) (X := X)) (topMap (A := A) (X := X) a) ha ⟨a, rfl⟩
      have hs : Nat.card (Top (A := A) (X := X)) = (Nat.card X).factorial := by
        rw [ht, Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_perm]
      exact (ne_of_lt horder) hs
    have hb := BinaryBlockUnsignedGeneralClassReserve.subnormal_class_card_le_class_budget_add_one_mul
      π hπ (fun x => (hsize x).le) hn B hB htop hns H hH
    have hh := (Nat.pow_le_pow_left hb 3).trans hbinary
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
    simpa only [hcard, Nat.mul_comm (Nat.card X) 2] using hh
  · have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L) ≤ 3 :=
      fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
    have hb := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ 3 hlocal B htop H hH
    have hh := (Nat.pow_le_pow_left hb 3).trans hternary
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
    simpa only [hcard, Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.PrimitiveTopSmallFibreClassBudget
