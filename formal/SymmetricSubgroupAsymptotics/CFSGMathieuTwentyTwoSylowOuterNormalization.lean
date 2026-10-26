import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenNormalizerCard
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenGeneration
import SymmetricSubgroupAsymptotics.OuterAutomorphismSubgroupExactCardinality
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityCancellation

/-! Actual Sylow-preserving automorphisms of the same original M22.
Only a conditional accepted-image incidence estimate is exported; no
finite candidate capacity or sporadic class census is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSylowOuterNormalization
open PrimitiveSocleRawStructure CFSGMathieuTwentyTwoElevenGeneration

private instance modelFinite : Finite CFSG.Models.Mathieu22 := Finite.of_injective
  (fun g : CFSG.Models.Mathieu22 => g.val) Subtype.val_injective
private instance automorphismFinite : Finite (MulAut CFSG.Models.Mathieu22) :=
  Finite.of_injective (fun f : MulAut CFSG.Models.Mathieu22 => (f : CFSG.Models.Mathieu22 → CFSG.Models.Mathieu22))
    DFunLike.coe_injective
private instance elevenPrime : Fact (Nat.Prime 11) := ⟨by decide⟩

theorem firstElement_ne_one : firstElement ≠ 1 := by
  intro h
  have hm : firstElement.val (0 : Fin 22) ≠ (0 : Fin 22) := by decide +kernel
  exact hm (congrArg (fun z : CFSG.Models.Mathieu22 => z.val (0 : Fin 22)) h)

theorem firstElement_order : orderOf firstElement = 11 :=
  orderOf_eq_prime firstElement_pow_eleven firstElement_ne_one

def selectedSylow : Sylow 11 CFSG.Models.Mathieu22 :=
  Sylow.ofCard (Subgroup.zpowers firstElement) (by
    rw [Nat.card_zpowers,firstElement_order,CFSGMathieuTwentyTwoActualOrder.card]
    decide +kernel)

theorem selectedSylow_eq_zpowers :
    (selectedSylow : Subgroup CFSG.Models.Mathieu22) = Subgroup.zpowers firstElement := rfl

def preservingAutomorphisms : Subgroup (MulAut CFSG.Models.Mathieu22) :=
  MulAction.stabilizer (MulAut CFSG.Models.Mathieu22) selectedSylow

theorem normalize_selectedSylow (f : MulAut CFSG.Models.Mathieu22) :
    ∃ g : CFSG.Models.Mathieu22, MulAut.conj g * f ∈ preservingAutomorphisms := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq CFSG.Models.Mathieu22 (f • selectedSylow) selectedSylow
  refine ⟨g,?_⟩
  change (MulAut.conj g * f) • selectedSylow = selectedSylow
  rw [mul_smul]
  exact hg

theorem inner_mem_preserving_iff (g : CFSG.Models.Mathieu22) :
    MulAut.conj g ∈ preservingAutomorphisms ↔
      g ∈ Subgroup.normalizer (selectedSylow : Set CFSG.Models.Mathieu22) :=
  Sylow.smul_eq_iff_mem_normalizer

theorem original_noncommutative : ¬ IsMulCommutative CFSG.Models.Mathieu22 := by
  intro h
  letI : IsMulCommutative CFSG.Models.Mathieu22 := h
  have hc : Subgroup.centralizer (selectedSylow : Set CFSG.Models.Mathieu22) = ⊤ := by
    apply top_unique
    intro g _
    apply Subgroup.mem_centralizer_iff.mpr
    intro z _
    exact mul_comm' z g
  have hh := CFSGMathieuTwentyTwoElevenNormalizerCard.centralizer_card_eq_eleven selectedSylow
  rw [hc,Subgroup.card_top,CFSGMathieuTwentyTwoActualOrder.card] at hh
  omega

theorem outer_mul_fiftyFive_eq_preservingAutomorphisms
    [IsSimpleGroup CFSG.Models.Mathieu22] :
    Nat.card (Outer CFSG.Models.Mathieu22) * 55 = Nat.card preservingAutomorphisms := by
  have hh := OuterAutomorphismSubgroupExactCardinality.outer_mul_subgroup_eq_automorphism_subgroup
    preservingAutomorphisms (Subgroup.normalizer (selectedSylow : Set CFSG.Models.Mathieu22))
    (CFSGOuterCardinalityCancellation.conj_injective original_noncommutative)
    normalize_selectedSylow inner_mem_preserving_iff
  rwa [CFSGMathieuTwentyTwoElevenNormalizerCard.normalizer_card_eq_fiftyFive] at hh

theorem closure_pair_eq_top :
    Subgroup.closure ({firstElement,secondElement} : Set CFSG.Models.Mathieu22) = ⊤ := by
  apply top_unique
  rw [←zpowers_sup_eq_top]
  exact sup_le
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inl rfl)))
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inr rfl)))

/-- The first coordinate is literally a nonidentity element of the
selected subgroup `zpowers firstElement`, rather than an ambient label. -/
def nontrivialFirstPowers := {z : selectedSylow // z.val ≠ (1 : CFSG.Models.Mathieu22)}

private instance nontrivialFirstPowersFinite : Finite nontrivialFirstPowers := by
  unfold nontrivialFirstPowers
  infer_instance

def evaluation (accepted : Finset CFSG.Models.Mathieu22)
    (haccepted : ∀ f : preservingAutomorphisms, f.val secondElement ∈ accepted) :
    preservingAutomorphisms → nontrivialFirstPowers × accepted := fun f =>
  (⟨⟨f.val firstElement,by
      have hm := Subgroup.smul_mem_pointwise_smul firstElement f.val
        (selectedSylow : Subgroup CFSG.Models.Mathieu22)
        (show firstElement ∈ (selectedSylow : Subgroup CFSG.Models.Mathieu22) from
          Subgroup.mem_zpowers firstElement)
      have he : f.val • (selectedSylow : Subgroup CFSG.Models.Mathieu22) =
          (selectedSylow : Subgroup CFSG.Models.Mathieu22) :=
        congrArg (fun P : Sylow 11 CFSG.Models.Mathieu22 => (P : Subgroup CFSG.Models.Mathieu22)) f.property
      rwa [he] at hm⟩,by
      intro he
      apply firstElement_ne_one
      apply f.val.injective
      exact he.trans (map_one f.val).symm⟩,
    ⟨f.val secondElement,haccepted f⟩)

theorem evaluation_injective (accepted : Finset CFSG.Models.Mathieu22)
    (haccepted : ∀ f : preservingAutomorphisms, f.val secondElement ∈ accepted) :
    Function.Injective (evaluation accepted haccepted) := by
  intro f h he
  apply Subtype.ext
  apply MulEquiv.ext
  intro z
  have hfirst : f.val firstElement = h.val firstElement :=
    congrArg (fun p : nontrivialFirstPowers × accepted => p.1.val.val) he
  have hsecond : f.val secondElement = h.val secondElement :=
    congrArg (fun p : nontrivialFirstPowers × accepted => p.2.val) he
  have hmaps : f.val.toMonoidHom = h.val.toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense closure_pair_eq_top
    rintro w (rfl|rfl)
    · exact hfirst
    · exact hsecond
  exact DFunLike.congr_fun hmaps z

theorem outer_mul_fiftyFive_le_accepted_product
    [IsSimpleGroup CFSG.Models.Mathieu22]
    (accepted : Finset CFSG.Models.Mathieu22)
    (haccepted : ∀ f : preservingAutomorphisms, f.val secondElement ∈ accepted) :
    Nat.card (Outer CFSG.Models.Mathieu22) * 55 ≤
      Nat.card nontrivialFirstPowers * accepted.card := by
  rw [outer_mul_fiftyFive_eq_preservingAutomorphisms]
  have hh := Nat.card_le_card_of_injective (evaluation accepted haccepted)
    (evaluation_injective accepted haccepted)
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_coe] using hh

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSylowOuterNormalization
