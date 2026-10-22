import Mathlib.GroupTheory.GroupAction.Primitive

/-! A transitive action containing a primitive action supported on more
than half the points is primitive. The supported subgroup fixes every
point outside its actual invariant subset. The proof is an explicit block
argument, independent of any simple-group classification or Jordan claim. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGSupportedPrimitiveAction
open MulAction

theorem isPreprimitive_of_large_supported_subaction
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    [IsPretransitive G X] (K : Subgroup G) (S : SubMulAction K X)
    [Nontrivial S] [IsPreprimitive K S]
    (hfix : ∀ (k : K) (x : X), x ∉ (S : Set X) → k • x = x)
    (hhalf : Nat.card X < (S : Set X).ncard * 2) : IsPreprimitive G X := by
  let a : S := Classical.arbitrary S
  apply IsPreprimitive.of_isTrivialBlock_base (a : X)
  intro B ha hB
  have hD : IsBlock K (Subtype.val ⁻¹' B : Set S) :=
    hB.subgroup.subtype_val_preimage
  rcases hD.subsingleton_or_eq_univ with hsmall | hfull
  · have heq : ∀ x ∈ B, x = (a : X) := by
      intro x hx
      by_cases hxS : x ∈ (S : Set X)
      · have hxD : (⟨x, hxS⟩ : S) ∈ (Subtype.val ⁻¹' B : Set S) := hx
        have haD : a ∈ (Subtype.val ⁻¹' B : Set S) := ha
        exact congrArg Subtype.val (hsmall hxD haD)
      · obtain ⟨b, hba⟩ := exists_ne a
        obtain ⟨k, hk⟩ := exists_smul_eq K a b
        have hkx : (k : G) • x = x := hfix k x hxS
        have hkB : (k : G) • B = B := hB.smul_eq_of_mem hx (hkx.symm ▸ hx)
        have hka : (k : G) • (a : X) ∈ B := by
          rw [← hkB]
          exact Set.smul_mem_smul_set ha
        have hkval : (k : G) • (a : X) = (b : X) := congrArg Subtype.val hk
        have hb : (b : X) ∈ B := hkval ▸ hka
        exact False.elim (hba (hsmall hb ha))
    exact Or.inl (fun x hx y hy => (heq x hx).trans (heq y hy).symm)
  · apply Or.inr
    apply hB.eq_univ_of_card_lt
    have hSB : (S : Set X) ⊆ B := by
      intro x hx
      have hm : (⟨x, hx⟩ : S) ∈ (Subtype.val ⁻¹' B : Set S) := by
        rw [hfull]
        exact Set.mem_univ _
      exact hm
    exact hhalf.trans_le (Nat.mul_le_mul_right 2 (Set.ncard_le_ncard hSB))

end SymmetricSubgroupAsymptotics.CFSGSupportedPrimitiveAction
