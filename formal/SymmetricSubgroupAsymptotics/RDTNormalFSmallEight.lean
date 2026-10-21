import SymmetricSubgroupAsymptotics.SmallBinaryNormalFBounds
import SymmetricSubgroupAsymptotics.BinaryDegreeEightExcessProfile
import SymmetricSubgroupAsymptotics.MarkedC4ActualExcessOneQuotientRank

/-! A single order/rank proof covers all original eight-point binary carriers
of order at most32 and every rank-preserving nonabelian normal quotient.
The group, denominator and source rank remain literal throughout. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.RDTNormalFSmallEight
open MarkedC4 MarkedC4.RDTExcessStructure MarkedC4.ActualNormalFMarkedPeel

 theorem excess_one_original_rank
    (G : Subgroup (Equiv.Perm (Fin 8))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 8,∃ g : G,g.val x=y)
    (hexcess : HasExcess G 8 1) : genRank G=3 := by
  letI : Group.IsNilpotent G := hG.isNilpotent
  obtain ⟨V,hV,hval⟩ := hexcess.1
  letI : V.Normal := hV
  have hVrank : normalGen V=3 := by
    norm_num at hval
    exact_mod_cast hval
  have hwhole : V=⊤ := BinaryDegreeEightExcessProfile.only_whole_of_excess_one
    G hG htrans hexcess V (by norm_num; omega)
  rw [hwhole,ActualExcessOneQuotientRank.normalGen_top_eq_genRank G] at hval
  norm_num at hval
  exact_mod_cast hval

 theorem quotient_packet
    (G : Subgroup (Equiv.Perm (Fin 8))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 8,∃ g : G,g.val x=y)
    (hcard : Nat.card G≤32) (hexcess : HasExcess G 8 1)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬∀ a b : G ⧸ N,a*b=b*a)
    (hrank : genRank (G ⧸ N)=genRank G) :
    ∃ F : Subgroup (G ⧸ N),F.Normal ∧
      commutatorLog F+centralLog F≤4 ∧ centralLog F≤2 := by
  letI : MulAction.IsPretransitive G (Fin 8) := ⟨htrans⟩
  have hnonabG : ¬∀ a b : G,a*b=b*a := by
    intro hcomm
    apply hnonab
    intro a b
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective N b
    simpa only [map_mul] using congrArg (QuotientGroup.mk' N) (hcomm x y)
  have hcenter : Nat.card (Subgroup.center G)≤4 :=
    SmallBinaryNormalFBounds.transitive_eight_center_card_le_four
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hnonabG
  have hQrank : 3≤genRank (G ⧸ N) := by
    rw [hrank,excess_one_original_rank G hG htrans hexcess]
  have hb := SmallBinaryNormalFBounds.quotient_top_log_bounds hG hcard hcenter N hQrank hnonab
  exact ⟨⊤,inferInstance,hb.1,hb.2⟩

end SymmetricSubgroupAsymptotics.RDTNormalFSmallEight
