import SymmetricSubgroupAsymptotics.AlternatingSupportedUnionGeneration

/-! An elementary overgroup trichotomy for an actual codimension-two
supported alternating group. This retains its inclusion as a hypothesis:
an arbitrary subgroup of small index is not asserted to contain it.
Only the literal natural carrier and conjugation of literal supports are
used. The argument is restricted to at least six original points. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.AlternatingCodimensionTwoOvergroups
open Equiv

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem preserves_pair_or_contains_codimension_one_or_top
    (H : Subgroup (alternatingGroup X)) (S : Finset X)
    (hsize : 6 ≤ Fintype.card X) (hcodim : S.card + 2 = Fintype.card X)
    (hS : (alternatingGroup.ofSubtype S).range ≤ H) :
    ((Sᶜ).card = 2 ∧ ∀ g : H, g.val • Sᶜ = Sᶜ) ∨
      (∃ U : Finset X, U.card + 1 = Fintype.card X ∧
        (alternatingGroup.ofSubtype U).range ≤ H) ∨ H = ⊤ := by
  by_cases hfix : ∀ g : H, g.val • S = S
  · left
    refine ⟨by rw [Finset.card_compl]; omega, ?_⟩
    intro g
    change g.val • (Finset.univ \ S) = Finset.univ \ S
    rw [Finset.smul_finset_sdiff, Finset.smul_finset_univ, hfix g]
  · obtain ⟨g, hg⟩ := not_forall.mp hfix
    let T : Finset X := g.val • S
    let U : Finset X := S ∪ T
    have hTcard : T.card = S.card := Finset.card_smul_finset g.val S
    have hTne : T ≠ S := hg
    have hT : (alternatingGroup.ofSubtype T).range ≤ H := by
      change (alternatingGroup.ofSubtype (g.val • S)).range ≤ H
      rw [← alternatingGroup.conj_smul_range_ofSubtype S g.val]
      intro k hk
      obtain ⟨u, hu, he⟩ :=
        (Subgroup.mem_smul_pointwise_iff_exists k (MulAut.conj g.val)
          (alternatingGroup.ofSubtype S).range).mp hk
      rw [← he]
      change g.val * u * g.val⁻¹ ∈ H
      exact H.mul_mem (H.mul_mem g.property (hS hu)) (H.inv_mem g.property)
    have hUle : U.card ≤ Fintype.card X := Finset.card_le_univ U
    have hinter : 2 ≤ (S ∩ T).card := by
      have hcount := Finset.card_union_add_card_inter S T
      change U.card + (S ∩ T).card = S.card + T.card at hcount
      omega
    have hU : (alternatingGroup.ofSubtype U).range ≤ H := by
      rw [show U = S ∪ T from rfl,
        ← AlternatingSupportedUnionGeneration.join_eq_union_of_two_le_inter_card S T hinter]
      exact sup_le hS hT
    have hSstrict : S ⊂ U := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_union_left, ?_⟩
      intro he
      have hTS : T ⊆ S := Finset.subset_union_right.trans he.symm.le
      exact hTne (Finset.eq_of_subset_of_card_le hTS hTcard.ge)
    have hScard : S.card < U.card := Finset.card_lt_card hSstrict
    by_cases hfull : U = Finset.univ
    · right; right
      apply top_unique
      intro k _
      apply hU
      apply (alternatingGroup.mem_range_ofSubtype_iff U k).mpr
      rw [hfull]
      exact Finset.subset_univ _
    · right; left
      have hUproper : U.card < Fintype.card X := by
        have hh := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hfull)
        simpa only [Finset.card_univ] using hh
      exact ⟨U, by omega, hU⟩

end SymmetricSubgroupAsymptotics.AlternatingCodimensionTwoOvergroups
