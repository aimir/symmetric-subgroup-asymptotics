import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.GroupTheory.Index

/-! A nonempty proper support in a transitive action has a genuine
proper set stabilizer. A second proper inclusion loses a further factor
two. These are actual subgroup-index bounds, without orbit-list or
transitive-group classification inputs. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.TransitiveSetStabilizerIndexBounds

theorem set_stabilizer_ne_top {G I : Type*} [Group G] [MulAction G I]
    (htrans : ∀ i j : I,∃g : G,g • i=j)
    (S : Set I) (hS : S.Nonempty) (hC : Sᶜ.Nonempty) :
    MulAction.stabilizer G S≠⊤ := by
  intro he
  obtain ⟨i,hi⟩ := hS
  obtain ⟨j,hj⟩ := hC
  obtain ⟨g,hg⟩ := htrans i j
  have hfix : g • S=S := by
    have hmem : g∈MulAction.stabilizer G S := by rw [he]; trivial
    exact hmem
  have hm : g • i∈g • S := Set.smul_mem_smul_set_iff.mpr hi
  rw [hfix,hg] at hm
  exact hj hm

theorem two_mul_set_stabilizer_card_le {G I : Type*} [Group G] [MulAction G I] [Finite G]
    (htrans : ∀ i j : I,∃g : G,g • i=j)
    (S : Set I) (hS : S.Nonempty) (hC : Sᶜ.Nonempty) :
    2*Nat.card (MulAction.stabilizer G S)≤Nat.card G := by
  let T := MulAction.stabilizer G S
  have hidx : 2≤T.index :=
    T.one_lt_index_of_ne_top (set_stabilizer_ne_top htrans S hS hC)
  calc
    _≤T.index*Nat.card T := Nat.mul_le_mul_right _ hidx
    _=Nat.card G := T.index_mul_card

theorem four_mul_card_le_of_strict_chain {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hAB : A<B) (hB : B≠⊤) :
    4*Nat.card A≤Nat.card G := by
  have hproper : A.subgroupOf B≠⊤ := by
    intro he
    exact (not_le_of_gt hAB) (Subgroup.subgroupOf_eq_top.mp he)
  have hAidx : 2≤A.relIndex B := (A.subgroupOf B).one_lt_index_of_ne_top hproper
  have hBidx : 2≤B.index := B.one_lt_index_of_ne_top hB
  have hidx : 4≤A.index := by
    calc
      _=2*2 := rfl
      _≤A.relIndex B*B.index := Nat.mul_le_mul hAidx hBidx
      _=A.index := Subgroup.relIndex_mul_index hAB.le
  calc
    _≤A.index*Nat.card A := Nat.mul_le_mul_right _ hidx
    _=Nat.card G := A.index_mul_card

end SymmetricSubgroupAsymptotics.TransitiveSetStabilizerIndexBounds
