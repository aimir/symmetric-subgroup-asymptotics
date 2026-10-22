import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime
import SymmetricSubgroupAsymptotics.CFSGTwoPSubgroupsSylowGeneration
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality

/-! Actual positive/negative p-subgroups supply good Sylow data once the
original positive normalizer is soluble and has no larger p-subgroup.
The displayed Sylow and conjugator are the original finite-group witnesses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem goodSylowPrime_of_positive_normalizer (U V : Subgroup G)
    (hU : IsPGroup p U) (hV : IsPGroup p V) (hgen : U⊔V=⊤)
    (hmax : ∀P : Subgroup G,IsPGroup p P→P≤Subgroup.normalizer (U : Set G)→P≤U)
    (hsol : IsSolvable (Subgroup.normalizer (U : Set G))) : GoodSylowPrime G p := by
  obtain ⟨P,g,hUP,hg⟩ := CFSGTwoPSubgroupsSylowGeneration.exists_conjugate_sylows U V hU hV hgen
  have hP : (P : Subgroup G)=U :=
    CFSGSylowNormalizerMaximality.maximal_of_normalizer_pGroups U hmax
      (P : Subgroup G) P.isPGroup' hUP
  refine ⟨Fact.out,P,g,?_,hg⟩
  change IsSolvable (Subgroup.normalizer ((P : Subgroup G) : Set G))
  rw [hP]
  exact hsol

end SymmetricSubgroupAsymptotics.CFSGReduction
