import SymmetricSubgroupAsymptotics.NaturalThreeNormalClassification
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! Any nontrivial original normal image in an actual transitive three-point
top leaves a quotient of order at most two. This is proved on the literal
subgroup of S3, without a transitive-group label or catalogue locator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairThreePointNormalTop

private theorem full_quotient_card_le_two (N : Subgroup (Equiv.Perm (Fin 3)))
    [N.Normal] (hne : N≠⊥) : Nat.card ((Equiv.Perm (Fin 3)) ⧸ N)≤2 := by
  rcases NaturalThreeNormalClassification.normal_trichotomy N inferInstance with h | h | h
  · exact False.elim (hne h)
  · rw [h,←Subgroup.index_eq_card,alternatingGroup.index_eq_two]
  · rw [h,←Subgroup.index_eq_card,Subgroup.index_top]
    decide

theorem cardinal_cases (T : Subgroup (Equiv.Perm (Fin 3)))
    [MulAction.IsPretransitive T (Fin 3)] : Nat.card T=3 ∨ Nat.card T=6 := by
  have hd : 3∣Nat.card T := by
    have h := (MulAction.stabilizer T (0 : Fin 3)).index_dvd_card
    simpa only [MulAction.index_stabilizer_of_transitive,Nat.card_fin] using h
  have hu : Nat.card T≤6 := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] using
      T.card_le_card_group
  have hp : 0<Nat.card T := Nat.card_pos
  obtain ⟨k,hk⟩ := hd
  omega

theorem quotient_card_le_two (T : Subgroup (Equiv.Perm (Fin 3)))
    [MulAction.IsPretransitive T (Fin 3)] (N : Subgroup T) [N.Normal]
    (hne : N≠⊥) : Nat.card (T ⧸ N)≤2 := by
  rcases cardinal_cases T with h3 | h6
  · letI : Fact (Nat.card T).Prime := ⟨by rw [h3]; decide⟩
    have hn : N=⊤ := (N.eq_bot_or_eq_top_of_prime_card).resolve_left hne
    rw [hn,←Subgroup.index_eq_card,Subgroup.index_top]
    decide
  · have ht : T=⊤ := Subgroup.eq_top_of_card_eq T (by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] using h6)
    let e : T ≃* Equiv.Perm (Fin 3) :=
      (MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv
    let M := N.map e.toMonoidHom
    letI : M.Normal := (inferInstance : N.Normal).map e.toMonoidHom e.surjective
    have hm : M≠⊥ := by
      intro hm
      have hk := (Subgroup.map_eq_bot_iff (H := N)).mp hm
      rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective] at hk
      exact hne (le_bot_iff.mp hk)
    have hc := Nat.card_congr (QuotientGroup.congr N M e rfl).toEquiv
    exact hc.le.trans (full_quotient_card_le_two M hm)

end SymmetricSubgroupAsymptotics.SixPairThreePointNormalTop
