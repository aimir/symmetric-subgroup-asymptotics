import SymmetricSubgroupAsymptotics.AbelianNormalSectionSemisimpleIntersection
import SymmetricSubgroupAsymptotics.NormalSectionProjectionEquiv
import SymmetricSubgroupAsymptotics.ChiefTernaryOrderBound

/-! Every chosen actual chief series pays its abelian ternary weight only
in the literal quotient by a specified semisimple normal subgroup. All
original projected intervals are retained, including repeated endpoints. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

/-- Abelian chief intervals inject into their actual projected intervals;
nonabelian original intervals have weight zero. Projected index valuations
telescope, so no multiplicity of the original simple socle is charged. -/
theorem actualChiefSeriesTernaryWeight_le_semisimpleQuotient_factorization
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] (C : SemisimpleNormalChart E)
    (s : ActualChiefSeries G) :
    actualChiefSeriesTernaryWeight s≤(Nat.card (G⧸E)).factorization 3 := by
  let pi := QuotientGroup.mk' E
  let f (i : Fin (s.length+1)) := (s.subgroup i).map pi
  have hf : Monotone f := fun i j hij => Subgroup.map_mono
    ((actualChiefSeries_strictMono s).monotone hij)
  have hsum := subgroupSeries_ternary_valuation_sum s.length f hf
  have h0 : f 0=⊥ := by simp only [f,s.head,Subgroup.map_bot]
  have hl : f (Fin.last s.length)=⊤ := by
    simp only [f,s.last,←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective E)
  rw [h0,hl,Subgroup.relIndex_bot_left,Subgroup.card_top] at hsum
  calc
    actualChiefSeriesTernaryWeight s ≤
        ∑ i : Fin s.length,((f i.castSucc).relIndex (f i.succ)).factorization 3 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hab : IsMulCommutative
          (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
      · letI := hab
        have hinter := semisimple_intersection_le_of_abelian_normalSection C
          (s.subgroup i.castSucc) (s.subgroup i.succ)
        have he := normalSectionProjection_relIndex E
          (s.subgroup i.castSucc) (s.subgroup i.succ) (s.step i).le hinter
        rw [chiefTernaryWeight,if_pos hab,
          normalChainQuotient_card (s.subgroup i.castSucc) (s.subgroup i.succ),he]
      · simp only [chiefTernaryWeight,if_neg hab]
        exact Nat.zero_le _
    _ = (Nat.card (G⧸E)).factorization 3 := hsum

end SymmetricSubgroupAsymptotics
