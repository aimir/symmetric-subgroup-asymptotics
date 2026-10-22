import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.Index

/-! Actual inner/outer order cancellation for a finite nonabelian
simple group. No quantitative automorphism estimate is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOuterCardinalityCancellation
open PrimitiveSocleRawStructure
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem conj_injective (hn : ¬ IsMulCommutative G) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  let c := (MulAut.conj : G →* MulAut G)
  rcases (inferInstance : c.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact c.ker_eq_bot_iff.mp hb
  · apply False.elim
    apply hn
    refine ⟨⟨fun x y => ?_⟩⟩
    have hx : x ∈ c.ker := by rw [ht]; trivial
    have he := congrArg (fun f : MulAut G => f y) (MonoidHom.mem_ker.mp hx)
    change x * y * x⁻¹ = y at he
    exact mul_inv_eq_iff_eq_mul.mp he

theorem outer_card_le_of_automorphism_bound (hn : ¬ IsMulCommutative G)
    (d : ℕ) (hbound : Nat.card (MulAut G) ≤ Nat.card G * d) :
    Nat.card (Outer G) ≤ d := by
  have hinner : Nat.card (Inner G) = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective hn)).toEquiv).symm
  have hcard := (Inner G).card_mul_index
  change Nat.card (Inner G) * Nat.card (Outer G) = Nat.card (MulAut G) at hcard
  rw [hinner] at hcard
  exact Nat.le_of_mul_le_mul_left (hcard.trans_le hbound) (Nat.card_pos (α := G))

end SymmetricSubgroupAsymptotics.CFSGOuterCardinalityCancellation
