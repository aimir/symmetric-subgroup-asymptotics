import SymmetricSubgroupAsymptotics.PrimePairWreathNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19AffineTop
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineSocles
import Mathlib.GroupTheory.IndexNormal

/-! The actual local order21 linear group has a prime Singer kernel and
order3 quotient. Its retained normal chain and a noncommuting pair give
an exact centerless normal-cover projection, hence wreath width two. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightRow19LinearWreath

open SemidirectProduct
open PrimitiveAffineDegreeTwoPairedEightAffineTops

abbrev R := PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.linearGroup

local instance sourceGroup : Group PrimitiveAffineEightFrameRow27TopCertificate.Source :=
  PrimitiveAffineEightFrameRow27TopCertificate.group

def singerElement : R := ⟨singer, PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.singer_mem⟩
def frobeniusElement : R :=
  ⟨PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.frobenius,
    PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.frobenius_mem⟩

theorem singerElement_ne_one : singerElement ≠ 1 := by
  intro h
  exact singer_ne_one (congrArg Subtype.val h)

instance : Nontrivial R := ⟨⟨singerElement, 1, singerElement_ne_one⟩⟩

theorem card : Nat.card R = 21 := by
  have htop : Nat.card PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.Top = 168 :=
    (Nat.card_congr PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv.toEquiv.symm).trans
      PrimitiveAffineEightFrameRow27TopCertificate.source_card
  have haff : Nat.card (AffineModel.Aff R) = 168 :=
    (Nat.card_congr PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.modelEquiv.toEquiv.symm).trans htop
  have hv : Nat.card (Multiplicative Vector) = 8 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hmul : 8 * Nat.card R = 168 := calc
    8 * Nat.card R = Nat.card (Multiplicative Vector × R) := by
      rw [Nat.card_prod, hv]
    _ = Nat.card (AffineModel.Aff R) :=
      (Nat.card_congr
        (SemidirectProduct.equivProd : AffineModel.Aff R ≃ Multiplicative Vector × R)).symm
    _ = 168 := haff
  omega

def singerKernel : Subgroup R := Subgroup.zpowers singerElement

theorem singerKernel_card : Nat.card singerKernel = 7 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hpow : singerElement ^ 7 = 1 := Subtype.ext singer_pow_seven
  change Nat.card (Subgroup.zpowers singerElement) = 7
  rw [Nat.card_zpowers, orderOf_eq_prime hpow singerElement_ne_one]

theorem singerKernel_index : singerKernel.index = 3 := by
  have h := singerKernel.card_mul_index
  rw [singerKernel_card, card] at h
  omega

instance singerKernel_normal : singerKernel.Normal :=
  Subgroup.normal_of_index_eq_minFac_card (by rw [singerKernel_index, card]; norm_num)

theorem singerKernel_ne_bot : singerKernel ≠ ⊥ := by
  intro h
  have hc := singerKernel_card
  rw [h, Subgroup.card_bot] at hc
  omega

theorem normal_total : ∀ N M : Subgroup R, N.Normal → M.Normal → N ≤ M ∨ M ≤ N :=
  normalSubgroups_total_of_surjective
    ((rightHom : AffineModel.Aff R →* R).comp
      PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.modelEquiv.toMonoidHom)
    (rightHom_surjective.comp PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.modelEquiv.surjective)
    PrimitiveAffineDegreeTwoPairedEightRow19NormalChain.top_normal_total

theorem singerKernel_normal_cover (N : Subgroup R) (hN : N.Normal) (hne : N ≠ ⊥) :
    singerKernel ≤ N := by
  letI := hN
  rcases normal_total singerKernel N inferInstance hN with h | h
  · exact h
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : IsSimpleGroup singerKernel := isSimpleGroup_of_prime_card singerKernel_card
  rcases (Subgroup.isSimpleGroup_iff.mp (inferInstance : IsSimpleGroup singerKernel)).2
      N h inferInstance with hb | he
  · exact (hne hb).elim
  · rw [he]

theorem center_eq_bot : Subgroup.center R = ⊥ := by
  by_contra h
  have hs : singerElement ∈ Subgroup.center R :=
    singerKernel_normal_cover _ inferInstance h (Subgroup.mem_zpowers singerElement)
  have he := congrArg (fun g : R ↦ (g : LinearGroup) firstVector)
    (Subgroup.mem_center_iff.mp hs frobeniusElement)
  have hne : (frobeniusElement * singerElement : R).val firstVector ≠
      (singerElement * frobeniusElement : R).val firstVector := by decide +kernel
  exact hne he

theorem quotient_card : Nat.card (R ⧸ singerKernel) = 3 := singerKernel_index

theorem wreath_normal_generating_pairs (N : Subgroup (C2Wreath.W R)) (hN : N.Normal) :
    ∃ x : Fin 2 → C2Wreath.W R, Subgroup.normalClosure (Set.range x) = N := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply C2Wreath.normal_generating_tuples_of_local_normal_cover
    (QuotientGroup.mk' singerKernel) (QuotientGroup.mk'_surjective singerKernel)
    center_eq_bot ?_ ?_ (by decide)
    (PrimePairWreathNormalGenerators.of_prime_card 3 quotient_card) N hN
  · simpa only [QuotientGroup.ker_mk'] using singerKernel_ne_bot
  · intro K hK hKb
    simpa only [QuotientGroup.ker_mk'] using singerKernel_normal_cover K hK hKb

end PrimitiveAffineDegreeTwoPairedEightRow19LinearWreath
end SymmetricSubgroupAsymptotics

end
