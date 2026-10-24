import SymmetricSubgroupAsymptotics.MinimalNormalIsotypicRelativeOrdinaryGenerators
import SymmetricSubgroupAsymptotics.MarkedC4SocleSurjectiveImage

/-! Ordinary sharing across TWO ACTUAL disjoint minimal normals. The
second factor is identified with its literal image in the first quotient;
Noether's third isomorphism retains the original quotient by their join.
The one/two-minimal-normal cover is not assumed to be the full socle here:
that actual primitive-action binding is a separate theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwoMinimalNormalIsotypicOrdinaryGenerators

variable {G T I J : Type} [Group G] [Finite G] [Group T] [Finite T] [Nontrivial T]
    [Fintype I] [Fintype J] (E F : Subgroup G) [E.Normal] [F.Normal]

theorem quotient_injective (hdis : Disjoint E F) :
    Function.Injective ((QuotientGroup.mk' E).subgroupMap F) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply Subtype.ext
  apply Subgroup.mem_bot.mp
  apply hdis.le_bot
  refine ⟨?_,x.property⟩
  exact (QuotientGroup.eq_one_iff x.val).mp (congrArg Subtype.val hx)

/-- The actual second normal subgroup and its marked first-quotient image. -/
def quotientFactorEquiv (hdis : Disjoint E F) : F ≃* F.map (QuotientGroup.mk' E) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' E).subgroupMap F)
    ⟨quotient_injective E F hdis,(QuotientGroup.mk' E).subgroupMap_surjective F⟩

theorem quotientFactorEquiv_apply (hdis : Disjoint E F) (x : F) :
    (quotientFactorEquiv E F hdis x : G ⧸ E) = (x.val : G ⧸ E) := rfl

variable (eE : E ≃* (I → T)) (eF : F ≃* (J → T)) (i : I) (j : J)

include eE eF i j in
theorem genRank_le (hE : IsMinimalNormalSubgroup E) (hF : IsMinimalNormalSubgroup F)
    (hdis : Disjoint E F) :
    MarkedC4.genRank G ≤ 2*MarkedC4.genRank T+MarkedC4.genRank (G ⧸ (E⊔F)) := by
  let q := QuotientGroup.mk' E
  let Fq : Subgroup (G ⧸ E) := F.map q
  let e : F ≃* Fq := quotientFactorEquiv E F hdis
  letI : Nontrivial F := F.nontrivial_iff_ne_bot.mpr hF.2.1
  letI : Nontrivial Fq := e.injective.nontrivial
  have hFqne : Fq ≠ ⊥ := Fq.nontrivial_iff_ne_bot.mp inferInstance
  have hFq := MarkedC4.SocleSurjectiveImage.minimalNormal_map q
    (QuotientGroup.mk'_surjective E) F hF hFqne
  let eFq : Fq ≃* (J → T) := e.symm.trans eF
  have hfirst := MinimalNormalIsotypicRelativeOrdinaryGenerators.genRank_le E eE i hE
  have hsecond := MinimalNormalIsotypicRelativeOrdinaryGenerators.genRank_le Fq eFq j hFq
  have hself : E.map q = ⊥ := by
    apply bot_unique
    rintro _ ⟨x,hx,rfl⟩
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr hx)
  have hmap : (E⊔F).map q = Fq := by
    rw [Subgroup.map_sup,hself,bot_sup_eq]
  let eq : ((G ⧸ E) ⧸ Fq) ≃* G ⧸ (E⊔F) :=
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient E (E⊔F) le_sup_left)
  have hquot : MarkedC4.genRank ((G ⧸ E) ⧸ Fq) = MarkedC4.genRank (G ⧸ (E⊔F)) :=
    CoprimeNilpotentProductGenerators.genRank_mulEquiv eq
  rw [hquot] at hsecond
  omega

include eE eF i j in
theorem exists_generating_finset (hE : IsMinimalNormalSubgroup E)
    (hF : IsMinimalNormalSubgroup F) (hdis : Disjoint E F) :
    ∃ s : Finset G, Subgroup.closure (s : Set G) = ⊤ ∧
      s.card ≤ 2*MarkedC4.genRank T+MarkedC4.genRank (G ⧸ (E⊔F)) := by
  obtain ⟨s,hs,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨s,hgen,hs.le.trans (genRank_le E F eE eF i j hE hF hdis)⟩

end SymmetricSubgroupAsymptotics.TwoMinimalNormalIsotypicOrdinaryGenerators
