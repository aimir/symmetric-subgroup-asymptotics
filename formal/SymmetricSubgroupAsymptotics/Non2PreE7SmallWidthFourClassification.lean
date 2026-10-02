import SymmetricSubgroupAsymptotics.Non2PreE7NonPairPhysicalFrontier

/-!
# Classification of retained width-four actions

A transitive subgroup of `S₄` has order divisible by four.  If it is proper,
its order is therefore `4`, `8`, or `12`; the first two possibilities are
2-groups.  Hence a retained non-2 action is literally the natural `A₄`
action or the full natural `S₄` action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Every retained transitive non-2 four-point action is literally natural
`A₄` or natural `S₄` on the catalogue labels. -/
theorem preE7NonPairAction_degreeFour_eq_alternating_or_top
    (U : PreE7NonPairActionClass 4) :
    preE7NonPairAction 4 U = alternatingGroup (Fin 4) ∨
      preE7NonPairAction 4 U = ⊤ := by
  let A := preE7NonPairAction 4 U
  letI : MulAction.IsPretransitive A (Fin 4) :=
    Non2TransitiveActionClass.representative_pretransitive U.1.1
  by_cases htop : A = ⊤
  · exact Or.inr htop
  · left
    have hindex : (MulAction.stabilizer A (0 : Fin 4)).index = 4 := by
      simpa only [Nat.card_fin] using
        MulAction.index_stabilizer_of_transitive A (0 : Fin 4)
    have hmul := (MulAction.stabilizer A (0 : Fin 4)).card_mul_index
    rw [hindex] at hmul
    have h4 : 4 ∣ Nat.card A :=
      ⟨Nat.card (MulAction.stabilizer A (0 : Fin 4)), by omega⟩
    have hle : Nat.card A ≤ 24 := by
      have h := Subgroup.card_le_card_group A
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at h ⊢
      exact h
    have hdiv : Nat.card A ∣ 24 := by
      have h := Subgroup.card_subgroup_dvd_card A
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at h ⊢
      exact h
    rw [Nat.card_eq_fintype_card] at hdiv
    have hne24 : Nat.card A ≠ 24 := by
      intro hcard
      apply htop
      apply Subgroup.eq_top_of_card_eq
      rw [hcard]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hnot2 : ¬ IsPGroup 2 A :=
      U.1.1.representative_not_isPGroup
    have hcard : Nat.card A = 12 := by
      rcases h4 with ⟨k, hk⟩
      have hkpos : 0 < k := by
        have hpos : 0 < Nat.card A := Nat.card_pos
        omega
      have hk6 : k ≤ 6 := by omega
      interval_cases k
      · exfalso
        apply hnot2
        apply IsPGroup.of_card (n := 2)
        norm_num at hk ⊢
        exact hk
      · exfalso
        apply hnot2
        apply IsPGroup.of_card (n := 3)
        norm_num at hk ⊢
        exact hk
      · norm_num at hk ⊢
        exact hk
      · have hf : Fintype.card A = 16 := by
          simpa [Nat.card_eq_fintype_card] using hk
        rw [hf] at hdiv
        norm_num at hdiv
      · have hf : Fintype.card A = 20 := by
          simpa [Nat.card_eq_fintype_card] using hk
        rw [hf] at hdiv
        norm_num at hdiv
      · exact False.elim (hne24 (by omega))
    have hindexA : A.index = 2 := by
      have h := A.card_mul_index
      have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
        norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
      rw [hcard, hperm] at h
      omega
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    exact hindexA

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
