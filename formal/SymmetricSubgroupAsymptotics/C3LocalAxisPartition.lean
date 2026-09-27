import SymmetricSubgroupAsymptotics.OutsideOrbitC3Physical

/-!
# Exact local axis partition for the regular C3 action

The regular ternary action has prime order, so every full local fusion
subgroup has either full or trivial first Goursat axis.  This exact partition
precedes the later split/nonsplit character division of the trivial-axis
branch and keeps an arbitrary survival predicate on the complete subgroup.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The regular ternary action has no intermediate subgroup. -/
theorem ternaryRegularAction_subgroup_eq_bot_or_top
    (N : Subgroup ternaryRegularAction) : N = ⊥ ∨ N = ⊤ := by
  have hdvd : Nat.card N ∣ 3 := by
    have h := Subgroup.card_subgroup_dvd_card N
    simpa only [ternaryRegularAction_card] using h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with hcard | hcard
  · exact Or.inl (Subgroup.eq_bot_of_card_eq N hcard)
  · right
    apply Subgroup.eq_top_of_card_eq N
    simpa only [ternaryRegularAction_card] using hcard

variable {Z : Type*}

abbrev C3AcceptedLocalFamily
    (P : Subgroup (ternaryRegularAction × Equiv.Perm Z) → Prop) :=
  {H : Subgroup (ternaryRegularAction × Equiv.Perm Z) //
    FusionAcceptedOrbitPredicate ternaryRegularAction P H}

abbrev C3DirectAxisLocalFamily
    (P : Subgroup (ternaryRegularAction × Equiv.Perm Z) → Prop) :=
  {H : C3AcceptedLocalFamily P // H.1.goursatFst = ⊤}

abbrev C3TrivialAxisLocalFamily
    (P : Subgroup (ternaryRegularAction × Equiv.Perm Z) → Prop) :=
  {H : C3AcceptedLocalFamily P // H.1.goursatFst = ⊥}

private theorem ternaryRegularAction_bot_ne_top :
    (⊥ : Subgroup ternaryRegularAction) ≠ ⊤ := by
  intro h
  have hc := congrArg (fun N : Subgroup ternaryRegularAction => Nat.card N) h
  change Nat.card (⊥ : Subgroup ternaryRegularAction) =
    Nat.card (⊤ : Subgroup ternaryRegularAction) at hc
  rw [Subgroup.card_bot,Subgroup.card_top,ternaryRegularAction_card] at hc
  omega

def c3NotDirectAxisEquivTrivialAxis
    (P : Subgroup (ternaryRegularAction × Equiv.Perm Z) → Prop) :
    {H : C3AcceptedLocalFamily P // H.1.goursatFst ≠ ⊤} ≃
      C3TrivialAxisLocalFamily P where
  toFun H := ⟨H.1,by
    rcases ternaryRegularAction_subgroup_eq_bot_or_top H.1.1.goursatFst with h | h
    · exact h
    · exact (H.2 h).elim⟩
  invFun H := ⟨H.1,by
    intro htop
    exact ternaryRegularAction_bot_ne_top (H.2.symm.trans htop)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact local partition, with the complete survival predicate retained in
both branches. -/
def c3AcceptedLocalAxisEquiv
    (P : Subgroup (ternaryRegularAction × Equiv.Perm Z) → Prop) :
    C3AcceptedLocalFamily P ≃
      C3DirectAxisLocalFamily P ⊕ C3TrivialAxisLocalFamily P :=
  (Equiv.sumCompl
    (fun H : C3AcceptedLocalFamily P => H.1.goursatFst = ⊤)).symm |>.trans
      (Equiv.sumCongr (Equiv.refl _) (c3NotDirectAxisEquivTrivialAxis P))

theorem c3AcceptedLocal_card_partition [Finite Z]
    (P : Subgroup (ternaryRegularAction × Equiv.Perm Z) → Prop) :
    Nat.card (C3AcceptedLocalFamily P) =
      Nat.card (C3DirectAxisLocalFamily P) +
        Nat.card (C3TrivialAxisLocalFamily P) := by
  rw [Nat.card_congr (c3AcceptedLocalAxisEquiv P),Nat.card_sum]

end SymmetricSubgroupAsymptotics

end
