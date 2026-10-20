import SymmetricSubgroupAsymptotics.BoundedSocleIsotypicSplit
import SymmetricSubgroupAsymptotics.NilpotentCentralizerGenerationStep
import SymmetricSubgroupAsymptotics.SolubleNormalSocleHeight
import SymmetricSubgroupAsymptotics.BoundedChiefSectionTransfer

/-! A bounded-chief-section substitute for the nilpotent-core theorem.
The constant depends on the fixed local section bound, and the ordinary
supplement has square-root growth in the original abelian-section budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration
open SolubleSocleConjugationModule AbelianSectionSize

/-- The original actual-group data imply a nilpotent core with an
ordinary supplement of size at most `L*(B!+1)*sqrt M`. This does not assert
the sharper published constant for unrestricted chief sections. -/
theorem bounded_nilpotent_core_generation
    (L : ℕ) {G : Type} [Group G] [Finite G] [IsSolvable G]
    (B M : ℕ) (hL : Height L G)
    (hB : BoundedChiefSections B G) (hM : SectionOmegaBound M G) :
    ∃ (K : Subgroup G) (S : Finset G), Group.IsNilpotent K ∧
      S.card≤L*(B.factorial+1)*M.sqrt ∧
      Subgroup.closure ((S : Set G)∪K)=⊤ := by
  induction L generalizing G B M with
  | zero =>
    letI : Subsingleton G := hL
    refine ⟨⊤,∅,inferInstance,by simp,?_⟩
    simp
  | succ L ih =>
    let V := finiteGroupSocle G
    letI : IsMulCommutative V := socle_isMulCommutative (G := G)
    letI : IsSemisimpleModule ℤ[G] (representation V).asModule :=
      socle_isSemisimple (G := G)
    obtain ⟨A,D,C,hA,hD,hC,hAD,hVC,hCD,hsmall,T,hT,hgenT⟩ :=
      bounded_semisimple_normal_split V B M hB hM
    letI : A.Normal := hA
    letI : D.Normal := hD
    letI : C.Normal := hC
    let W : Subgroup C := V.subgroupOf C
    let Q := C⧸W
    let f : C →* Q := QuotientGroup.mk' W
    have hf : Function.Surjective f := QuotientGroup.mk'_surjective W
    have hker : f.ker=V.subgroupOf C := QuotientGroup.ker_mk' W
    let q := QuotientGroup.mk' V
    let g : C →* G⧸V := q.comp C.subtype
    have hgker : g.ker=W := by
      ext c
      change q (c : G)=1 ↔ (c : G)∈V
      exact QuotientGroup.eq_one_iff (c : G)
    have hrange : g.range=C.map q := by
      rw [MonoidHom.range_comp,Subgroup.range_subtype]
    letI : g.range.Normal := by
      rw [hrange]
      exact Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective V)
    have hheightRange : Height L g.range := height_normal g.range hL
    have hheightQ : Height L Q := by
      have h := (height_equiv (QuotientGroup.quotientKerEquivRange g)).mpr hheightRange
      exact (height_equiv (QuotientGroup.quotientMulEquivOfEq hgker)).mp h
    have hBQ : BoundedChiefSections B Q :=
      (hB.of_injective C.subtype Subtype.val_injective).of_surjective f hf
    have hMQ : SectionOmegaBound M Q :=
      (hM.of_injective C.subtype Subtype.val_injective).of_surjective f hf
    obtain ⟨J,SQ,hJ,hSQ,hgenQ⟩ := ih B M hheightQ hBQ hMQ
    letI : Group.IsNilpotent J := hJ
    obtain ⟨K,S,hK,hS,hgen⟩ := nilpotent_centralizer_generation_step
      A D V C hAD hVC hCD f hf hker J SQ hgenQ T hgenT M.sqrt hsmall
    refine ⟨K,S,hK,?_,hgen⟩
    calc
      S.card≤SQ.card+T.card+M.sqrt := hS
      _ ≤ L*(B.factorial+1)*M.sqrt+B.factorial*M.sqrt+M.sqrt := by omega
      _ = (L+1)*(B.factorial+1)*M.sqrt := by ring

end SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration
