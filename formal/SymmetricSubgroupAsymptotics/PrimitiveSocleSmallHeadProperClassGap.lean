import SymmetricSubgroupAsymptotics.PrimitiveSocleWeakClassSquareProperGap
import SymmetricSubgroupAsymptotics.ComponentClassCubeLooseWreathExtraGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleActualQuotientGcdBudget

/-! Small heads retain the actual faithful-action quotient at their
minimum degree. Larger degrees and multiple factors absorb the complete
outer factor. The hypotheses are model metadata and scalar inequalities;
no subnormal subgroup class budget is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_small_head
    (D : NonaffineData G X) (b s c o : ℕ) (hb : 5 ≤ b)
    (horder : Nat.card D.Simple=s)
    (hclass : Nat.card (ConjClasses D.Simple) ≤ c)
    (houter : Nat.card (Outer D.Simple) ≤ o)
    (hindex : ∀ K : Subgroup D.Simple, K ≠ ⊤ → b ≤ K.index)
    (hsquare : b^2 ≤ s) (hqpos : 0 < b.factorial/s)
    (hsmall : (c*(b.factorial/s))^3 ≤ 8*5^(b-2))
    (hlarge : (c*o)^3 ≤ 8*5^(b-1))
    (hmulti : (c*o)^3 ≤ 5^(b+1))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  have hn := D.degree_lower_of_proper_index_lower b hindex
  by_cases hone : D.factorCount=1
  · have htwo := D.twice_proper_subnormal_class_card_le_outer hone H hH hne
    have htwo' : 2*Nat.card (ConjClasses H) ≤ c*o :=
      htwo.trans (Nat.mul_le_mul hclass houter)
    by_cases hdegree : Nat.card X=b
    · have hdvd := PrimitiveSocleActualQuotientGcdBudget.quotient_card_dvd_degree_factorial_div_simple D hone
      rw [hdegree, horder] at hdvd
      have hquot := Nat.le_of_dvd hqpos hdvd
      have hactual := D.twice_proper_subnormal_class_card_le_socle_quotient hone H hH hne
      have hactual' : 2*Nat.card (ConjClasses H) ≤ c*(b.factorial/s) :=
        hactual.trans ((Nat.mul_le_mul hquot hclass).trans_eq (Nat.mul_comm _ _))
      have hp : 8*Nat.card (ConjClasses H)^3 ≤ (c*(b.factorial/s))^3 := by
        simpa only [mul_pow, show (2 : ℕ)^3=8 by decide] using Nat.pow_le_pow_left hactual' 3
      rw [hdegree]
      have hh := hp.trans hsmall
      omega
    · have hp : 8*Nat.card (ConjClasses H)^3 ≤ (c*o)^3 := by
        simpa only [mul_pow, show (2 : ℕ)^3=8 by decide] using Nat.pow_le_pow_left htwo' 3
      have he : b-1 ≤ Nat.card X-2 := by omega
      have hh := hp.trans (hlarge.trans (Nat.mul_le_mul_left 8
        (Nat.pow_le_pow_right (by decide) he)))
      omega
  have hk : 2 ≤ D.factorCount := by have hpos := D.factorCount_pos; omega
  have hbase : (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple))^3 ≤ 5^(b+1) :=
    (Nat.pow_le_pow_left (Nat.mul_le_mul hclass houter) 3).trans hmulti
  have hw := ComponentClassCubeLooseWreathExtraGap.wreath_class_cube_le
    (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple)) b D.factorCount hb hk hbase
  have hpower : b^D.factorCount ≤ Nat.card X := by
    rcases D.indexForm with ⟨K, hK, hdegree⟩ | ⟨a, hka, hdegree⟩
    · exact (Nat.pow_le_pow_left (hindex K hK) D.factorCount).trans_eq hdegree.symm
    · rw [hdegree]
      calc
        b^D.factorCount ≤ b^(2*a) := Nat.pow_le_pow_right (by omega) hka
        _ = (b^2)^a := pow_mul b 2 a
        _ ≤ (Nat.card D.Simple)^a := Nat.pow_le_pow_left (hsquare.trans_eq horder.symm) a
  exact (Nat.pow_le_pow_left (D.subnormal_class_card_le_outer_wreath H hH) 3).trans
    (hw.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hpower 2)))

theorem NonaffineData.proper_subnormal_class_cube_le_of_small_model_head
    (D : NonaffineData G X) (S : Type) [Group S] [Finite S]
    (e : D.Simple ≃* S) (b s c o : ℕ) (hb : 5 ≤ b)
    (horder : Nat.card S=s) (hclass : Nat.card (ConjClasses S) ≤ c)
    (houter : Nat.card (Outer S) ≤ o)
    (hindex : ∀ K : Subgroup S, K ≠ ⊤ → b ≤ K.index)
    (hsquare : b^2 ≤ s) (hqpos : 0 < b.factorial/s)
    (hsmall : (c*(b.factorial/s))^3 ≤ 8*5^(b-2))
    (hlarge : (c*o)^3 ≤ 8*5^(b-1)) (hmulti : (c*o)^3 ≤ 5^(b+1))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  refine D.proper_subnormal_class_cube_le_of_small_head b s c o hb
    ((Nat.card_congr e.toEquiv).trans horder) ?_ ?_ ?_
    hsquare hqpos hsmall hlarge hmulti H hH hne
  · exact (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)).trans hclass
  · rw [CFSGReduction.outer_card_congr e]
    exact houter
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hh := hindex (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rwa [hi] at hh

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
