import SymmetricSubgroupAsymptotics.PerfectTransitiveActionCentralizer
import SymmetricSubgroupAsymptotics.FinitePermutationFixedComplementEmbedding
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.Perm.Finite

/-! A nontrivial perfect action with gap27 cannot commute faithfully with
a group of order9 in fewer than33 points. Actual orbits and their exact
complements are retained throughout. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PerfectActionTernaryPairPacking
open PerfectTransitiveActionCentralizer
variable {L X : Type*} [Group L] [Finite X] [MulAction L X]

private theorem orbit_card_ge_gap {d : ℕ} (hgap : FiniteActionGap L d)
    (g : L) (x : X) (hx : g • x≠x) : d≤Nat.card (MulAction.orbit L x) := by
  by_contra hh
  have he := finite_action_eq_one_of_gap hgap
    (MulAction.toPermHom L (MulAction.orbit L x)) (show Nat.card (MulAction.orbit L x)<d by omega)
  have hfix := congrArg
    (fun p : Equiv.Perm (MulAction.orbit L x) => (p ⟨x,MulAction.mem_orbit_self x⟩).val)
      (DFunLike.congr_fun he g)
  exact hx hfix

private theorem orbit_card_add_le (x y : X)
    (hd : Disjoint (MulAction.orbit L x) (MulAction.orbit L y)) :
    Nat.card (MulAction.orbit L x)+Nat.card (MulAction.orbit L y)≤Nat.card X := by
  let f : (MulAction.orbit L x)⊕(MulAction.orbit L y) → X :=
    Sum.elim Subtype.val Subtype.val
  have hf : Function.Injective f := by
    intro a b he
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext he)
      | inr b =>
        change a.val=b.val at he
        have hh : b.val∈MulAction.orbit L x := he ▸ a.property
        exact False.elim ((Set.disjoint_left.mp hd) hh b.property)
    | inr a =>
      cases b with
      | inl b =>
        change a.val=b.val at he
        have hh : a.val∈MulAction.orbit L x := he.symm ▸ b.property
        exact False.elim ((Set.disjoint_left.mp hd) hh a.property)
      | inr b => exact congrArg Sum.inr (Subtype.ext he)
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_sum] using hh

/-- All capacity here is structural: a faithful order9 permutation image,
actual commutation, and the acting group's proved finite-action gap. -/
theorem card_ge_thirtyThree [Group.IsPerfect L] {P : Type*} [Group P] [Finite P]
    (hgap : FiniteActionGap L 27)
    (hmove : ∃ g : L, ∃ x : X, g • x≠x)
    (f : P →* Equiv.Perm X) (hf : Function.Injective f) (hP : Nat.card P=9)
    (hc : ∀ (p : P) (g : L) (x : X), f p (g • x)=g • f p x) :
    33≤Nat.card X := by
  classical
  by_contra hbad
  have hn : Nat.card X≤32 := by omega
  obtain ⟨g,x,hx⟩ := hmove
  let O : Set X := MulAction.orbit L x
  have hO : 27≤Nat.card O := orbit_card_ge_gap hgap g x hx
  have hcardO : Nat.card O≤Nat.card X := Nat.card_le_card_of_injective
    (fun y : O => y.val) Subtype.val_injective
  have hpres (p : P) (y : X) (hy : y∈O) : f p y∈O := by
    have hmx : g • f p x≠f p x := by
      intro hh
      apply hx
      apply (f p).injective
      exact (hc p g x).trans hh
    have hOx : MulAction.orbit L (f p x)=O := by
      rcases MulAction.orbit.eq_or_disjoint (G := L) x (f p x) with he | hd
      · exact he.symm
      · have hsum := orbit_card_add_le x (f p x) hd
        have hother := orbit_card_ge_gap hgap g (f p x) hmx
        change Nat.card O+Nat.card (MulAction.orbit L (f p x))≤Nat.card X at hsum
        omega
    change f p y∈MulAction.orbit L x
    rcases MulAction.mem_orbit_iff.mp hy with ⟨h,rfl⟩
    rw [hc p h x]
    change h • f p x∈O
    rw [←hOx]
    exact MulAction.mem_orbit (f p x) h
  have hfix : ∀ p : P, ∀ y∈O, f p y=y := by
    intro p y hy
    let c : Equiv.Perm O := (f p).subtypePermOfFintype (hpres p)
    have he : c=1 := centralizing_perm_eq_one_of_card_lt_twice_gap hgap
      (show Nat.card O<2*27 by omega) c (by
        intro h z
        apply Subtype.ext
        exact hc p h z.val)
    exact congrArg (fun q : Equiv.Perm O => (q ⟨y,hy⟩).val) he
  have hcomp : Nat.card {y : X // y∉O}≤5 := by
    letI : Fintype X := Fintype.ofFinite X
    letI : Fintype O := Fintype.ofFinite O
    letI : Fintype {y : X // y∉O} := Fintype.ofFinite _
    have he : Nat.card {y : X // y∉O}=Nat.card X-Nat.card O := by
      simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_compl (fun y : X => y∈O)
    omega
  exact FinitePermutationFixedComplementEmbedding.nine_not_in_complement_of_card_le_five
    f O hfix hf hP hcomp

end SymmetricSubgroupAsymptotics.PerfectActionTernaryPairPacking
