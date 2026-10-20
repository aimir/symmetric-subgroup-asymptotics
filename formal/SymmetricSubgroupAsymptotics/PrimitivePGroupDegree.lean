import SymmetricSubgroupAsymptotics.PGroupPrimeIndexChain
import Mathlib.GroupTheory.GroupAction.Primitive

/-! A nontrivial primitive action of a finite p-group has degree p. This
uses the actual point stabilizer and its prime-index cover, without any
classification of permutation groups. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem primitive_pGroup_degree {G X : Type} [Group G] [Finite G]
    [MulAction G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (x : X) : Nat.card X = p := by
  have hc : MulAction.stabilizer G x ⋖ ⊤ :=
    (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) x).covBy_top
  have h := pGroup_subgroupCover_relIndex hG (MulAction.stabilizer G x) ⊤ hc
  simpa only [Subgroup.relIndex_top_right,
    MulAction.index_stabilizer_of_transitive G x] using h

theorem primitive_eight_not_binary {G X : Type} [Group G] [Finite G]
    [MulAction G X] [MulAction.IsPreprimitive G X] [Finite X]
    (hX : Nat.card X = 8) : ¬ IsPGroup 2 G := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  intro hG
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have h := primitive_pGroup_degree hG x
  omega

end SymmetricSubgroupAsymptotics

end
