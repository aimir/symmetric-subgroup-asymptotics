import SymmetricSubgroupAsymptotics.BinaryTargetOrderEnvelope
import SymmetricSubgroupAsymptotics.JointSourceGraphs

/-!
# Same-source moments for the binary target-order envelope

All binary characters stay on one complete original subgroup J. The target
order envelope can therefore use a marker of degree 2*log2(|Q|), even when
Q has no faithful permutation action of that degree. This is a counting
majorant, not a replacement action for the original Q. A strict physical
fusion gap requires that marker degree to be smaller than the original
width; the central-involution character criterion alone does not imply it.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics

/-- The complete a-character marker moment on the same original J. -/
theorem binaryTargetOrder_marker_moment_le (a b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), (2^(a * binaryCharacterRank J))^q) ≤
      subgroupCount (b + q*(2*a)) := by
  have h := jointSourceHom_moment_le (binaryMarkerFiniteAction a)
    (binaryMarkerFiniteAction_injective a)
    (MonoidHom.id (Multiplicative (Fin a → ZMod 2))) Function.surjective_id b q
  simpa only [binaryAbelianizationGroupHom_card, Module.finrank_pi,
    Fintype.card_fin, Nat.mul_comm] using h

/-- All actual Hom counts inherit the same-source marker moment. -/
theorem binaryTargetOrder_hom_moment_le {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (J →* Q))^q) ≤
      subgroupCount (b + q*(2*Nat.log 2 (Nat.card Q))) := by
  apply le_trans _ (binaryTargetOrder_marker_moment_le (Nat.log 2 (Nat.card Q)) b q)
  apply Finset.sum_le_sum
  intro J _
  exact pow_le_pow_left₀ (Nat.zero_le _) (binaryTargetOrder_hom_card_le hQ) q

/-- This fixed target determines its weight before any exterior-source
sum or survival test. No target automorphism quotient is taken. -/
def binaryTargetOrderWeight (Q J : Type*) [Group Q] [Group J] : ℝ :=
  (2 : ℝ)^(Nat.log 2 (Nat.card Q) * binaryCharacterRank J)

theorem binaryTargetOrderWeight_nonneg (Q J : Type*) [Group Q] [Group J] :
    0 ≤ binaryTargetOrderWeight Q J := by
  unfold binaryTargetOrderWeight
  positivity

/-- The same weight controls every surviving set of literal onto maps.
Its translation factors were retained at every actual central-series step. -/
theorem binaryTargetOrder_survival_le_weight
    {J Q : Type*} [Group J] [Finite J] [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (S : GroupEpimorphism J Q → Prop) :
    (Nat.card {f : GroupEpimorphism J Q // S f} : ℝ) ≤ binaryTargetOrderWeight Q J := by
  unfold binaryTargetOrderWeight
  exact_mod_cast binaryTargetOrder_surviving_epi_card_le hQ S

/-- The canonical real-valued moment uses exactly 2a new physical marker
points per column. The original exterior appears once, not once per column. -/
theorem binaryTargetOrderWeight_moment_le (Q : Type*) [Group Q] (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), (binaryTargetOrderWeight Q J)^q) ≤
      (subgroupCount (b + q*(2*Nat.log 2 (Nat.card Q))) : ℝ) := by
  unfold binaryTargetOrderWeight
  exact_mod_cast binaryTargetOrder_marker_moment_le (Nat.log 2 (Nat.card Q)) b q

end SymmetricSubgroupAsymptotics
