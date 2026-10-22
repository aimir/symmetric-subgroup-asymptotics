import SymmetricSubgroupAsymptotics.CFSGSymmetricSylowNormalizerStep

/-! Every Sylow two-subgroup of a finite symmetric group is
self-normalizing. The proof inducts on the literal permutation degree,
using the canonical matching and its actual cycle action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
universe u

namespace SymmetricSubgroupAsymptotics.CFSGSymmetricSylowSelfNormalizer
open Equiv CFSGSymmetricSylowNormalizerStep CFSGSymmetricSylowCanonicalMatching

private theorem normalizer_eq_self_of_degree (n : ℕ) :
    ∀ {X : Type u} [Fintype X] [DecidableEq X], Fintype.card X = n →
      ∀ P : Sylow 2 (Perm X), Subgroup.normalizer (P : Set (Perm X)) = P := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X _ _ hcard P
    by_cases hn : n = 0
    · letI : IsEmpty X := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      exact Subsingleton.elim _ _
    · have hpos : 0 < Fintype.card X := by omega
      apply normalizer_eq_self_of_cycle_action P
      intro Q
      exact ih _ ((matching_cycle_degree_lt P hpos).trans_eq hcard) rfl Q

theorem normalizer_eq_self
    {X : Type u} [Fintype X] [DecidableEq X] (P : Sylow 2 (Perm X)) :
    Subgroup.normalizer (P : Set (Perm X)) = P :=
  normalizer_eq_self_of_degree (Fintype.card X) rfl P

theorem normalizer_isPGroup
    {X : Type u} [Fintype X] [DecidableEq X] (P : Sylow 2 (Perm X)) :
    IsPGroup 2 (Subgroup.normalizer (P : Set (Perm X))) := by
  rw [normalizer_eq_self P]
  exact P.isPGroup'

end SymmetricSubgroupAsymptotics.CFSGSymmetricSylowSelfNormalizer
