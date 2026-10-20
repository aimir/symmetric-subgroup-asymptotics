import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators
import SymmetricSubgroupAsymptotics.CyclicQuotientSocles
import SymmetricSubgroupAsymptotics.SubdirectPairNormalGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import Mathlib.Tactic.NormNum

/-! All actual subgroups of S3 are normally cyclic. Lagrange's theorem
reduces a proper subgroup to order dividing two or three. The full group
uses its checked normal chain. Consequently an actual subgroup of S3 × S3
has uniform normal-generator bound two, with arbitrary correlations
between its coordinate ranges retained. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SymmetricThreeSubgroupNormalGenerators

abbrev S3 := Equiv.Perm (Fin 3)

theorem normal_generating_singletons (H : Subgroup S3) :
    ∀ N : Subgroup H, N.Normal →
      ∃ x : Fin 1 → H, Subgroup.normalClosure (Set.range x) = N := by
  have hcard : Nat.card S3 = 6 := by
    rw [Nat.card_perm,Nat.card_fin]
    decide
  have hd : Nat.card H ∣ 6 := hcard ▸ H.card_subgroup_dvd_card
  have hb : Nat.card H ≤ 6 := Nat.le_of_dvd (by decide) hd
  have hcases : Nat.card H = 6 ∨ Nat.card H ∣ 2 ∨ Nat.card H ∣ 3 := by
    interval_cases hc : Nat.card H <;> norm_num at *
  rcases hcases with hfull | htwo | hthree
  · have hH : H = ⊤ := H.eq_top_of_card_eq (hfull.trans hcard.symm)
    let e : H ≃* S3 := MulEquiv.ofBijective H.subtype
      ⟨Subtype.coe_injective,fun x => ⟨⟨x,by rw [hH]; trivial⟩,rfl⟩⟩
    exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
      (normal_generating_singletons_of_finite_normal_total
        NaturalFourNormalChains.symmetric_three_normal_total)
  · letI : IsCyclic H := isCyclic_of_card_dvd_prime (p := 2) htwo
    exact normal_generating_singletons_of_isCyclic
  · letI : IsCyclic H := isCyclic_of_card_dvd_prime (p := 3) hthree
    exact normal_generating_singletons_of_isCyclic

theorem normalGen_le (H : Subgroup S3) (N : Subgroup H) [N.Normal] :
    MarkedC4.normalGen N ≤ 1 := by
  obtain ⟨x,hx⟩ := normal_generating_singletons H N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem normal_generating_pairs_of_pair
    {G : Type} [Group G] (f g : G →* S3)
    (hjoint : Function.Injective (fun x : G => (f x,g x))) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin 2 → G, Subgroup.normalClosure (Set.range x) = N := by
  apply normal_generating_tuples_subdirect_pair f.rangeRestrict g.rangeRestrict
    f.rangeRestrict_surjective g.rangeRestrict_surjective ?_
    (normal_generating_singletons f.range) (normal_generating_singletons g.range)
  intro x y h
  apply hjoint
  exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h)

theorem pair_normalGen_le
    {G : Type} [Group G] (f g : G →* S3)
    (hjoint : Function.Injective (fun x : G => (f x,g x)))
    (N : Subgroup G) [N.Normal] : MarkedC4.normalGen N ≤ 2 := by
  obtain ⟨x,hx⟩ := normal_generating_pairs_of_pair f g hjoint N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem pair_quotientSocle
    {G : Type} [Group G] (f g : G →* S3)
    (hjoint : Function.Injective (fun x : G => (f x,g x)))
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_pairs_of_pair f g hjoint) N

end SymmetricSubgroupAsymptotics.SymmetricThreeSubgroupNormalGenerators

end
