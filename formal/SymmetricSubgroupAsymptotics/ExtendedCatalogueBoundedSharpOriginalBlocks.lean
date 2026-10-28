import SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharpSmallActions
import SymmetricSubgroupAsymptotics.BoundedSharpJankoTwoHeisenbergSingerCompleteCFSG
import SymmetricSubgroupAsymptotics.ExtendedCatalogueSmallDegreeModels
import SymmetricSubgroupAsymptotics.ExtendedCatalogueOddOrderSolvability
import SymmetricSubgroupAsymptotics.TraceyPublished2018PermutationBundle

/-! Internal bounded-sharp assembly for the actual extended classification target.
The proof reuses the literal original action, residual structures, failed-half
witnesses, all tag guards, and checked finite prime certificates. Only the
classification funnels and the odd-order backend change. The raw Y443 branch
is excluded by degree before entering any old-model residual. This module does
not construct Classification or add it as a public T1 assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.LargePrimeSocleQuotientGenerators
open _root_.SymmetricSubgroupAsymptotics.LargePrimeSocleQuotientGenerators
open SingleCycleNormalizerQuotientGenerators
open PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] {p : ℕ} [Fact p.Prime]

theorem quotient_genRank_le_fixedBudget (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (S : Subgroup G) [S.Normal] (hpdiv : p ∣ Nat.card S)
    (hnot : ¬p^2 ∣ Nat.card S) (hdegree : Nat.card X<2*p)
    (hfixed : Nat.card X-p ≤ 10) :
    MarkedC4.genRank (G ⧸ S) ≤ 1+_root_.SymmetricSubgroupAsymptotics.TenPointHalfDegreeCompleteCFSG.fixedBudget (Nat.card X-p) := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := S) p hpdiv
  have hU : IsPGroup p (Subgroup.zpowers a) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,ha,pow_one]
  obtain ⟨P,hP⟩ := hU.exists_le_sylow
  have haP : a ∈ P := hP (Subgroup.mem_zpowers a)
  have hPcard : Nat.card P=p :=
    SimpleInvolutionPrimeCycleGoodSylow.sylow_card_of_member_order P a haP ha hnot
  have hPgen : (P : Subgroup S)=Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge hP (by rw [Nat.card_zpowers,ha,hPcard])).symm
  let H : Subgroup G := (P : Subgroup S).map S.subtype
  have hHgen : H=Subgroup.zpowers (a : G) := by
    dsimp only [H]
    rw [hPgen,MonoidHom.map_zpowers]
    rfl
  have hHcard : Nat.card H=p := by
    dsimp only [H]
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hPcard
  letI : IsCyclic (MulAut H) := cyclic_aut_of_prime_card H p hHcard
  let rho : G →* Equiv.Perm X := MulAction.toPermHom G X
  have horder : orderOf (rho (a : G))=p :=
    (orderOf_injective rho MulAction.toPerm_injective (a : G)).trans
      ((Subgroup.orderOf_coe a).trans ha)
  letI : Fintype X := Fintype.ofFinite X
  have hc : (rho (a : G)).IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [horder]; exact Fact.out) (by rw [horder,←Nat.card_eq_fintype_card]; exact hdegree)
  have htype : (rho (a : G)).cycleType={p} := by
    rw [hc.cycleType,←hc.orderOf,horder]
  let beta : Normalizer H →* G ⧸ S :=
    (QuotientGroup.mk' S).comp (Subgroup.normalizer (H : Set G)).subtype
  have hbeta : Function.Surjective beta := by
    apply MonoidHom.range_eq_top.mp
    change ((QuotientGroup.mk' S).comp (Subgroup.normalizer (H : Set G)).subtype).range=⊤
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
    have hcod : Codisjoint (Subgroup.normalizer (H : Set G)) (QuotientGroup.mk' S).ker := by
      rw [QuotientGroup.ker_mk']
      exact codisjoint_iff.mpr (Sylow.normalizer_sup_eq_top P)
    rw [(Subgroup.map_eq_range_iff).mpr hcod]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective S)
  have hHleS : H ≤ S := by
    rintro g ⟨b,hb,rfl⟩
    exact b.property
  have hkill : H.subgroupOf (Normalizer H) ≤ beta.ker := by
    intro u hu
    change u.val ∈ (QuotientGroup.mk' S).ker
    rw [QuotientGroup.ker_mk']
    exact hHleS hu
  have hcard : Nat.card (Fixed (X := X) H)=Nat.card X-p := fixed_card H (a : G) hHgen p htype
  have hb := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointHalfDegreeCompleteCFSG.faithful_genRank_le_fixedBudget hclass
    (G := (fixedHom (X := X) H).range) (X := Fixed (X := X) H)
    (by rw [hcard]; exact hfixed)
  rw [hcard] at hb
  exact quotient_genRank_le_one_add (X := X) H (a : G) hHgen hc beta hbeta hkill _ hb


theorem nonaffine_genRank_le_fixedBudget (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (D : NonaffineData G X) (hsmall : Nat.card X<25)
    (hhead : MarkedC4.genRank D.Simple ≤ 2) (hpdiv : p ∣ Nat.card D.Simple)
    (hnot : ¬p^2 ∣ Nat.card D.Simple) (hdegree : Nat.card X<2*p)
    (hfixed : Nat.card X-p ≤ 10) :
    MarkedC4.genRank G ≤ 3+_root_.SymmetricSubgroupAsymptotics.TenPointHalfDegreeCompleteCFSG.fixedBudget (Nat.card X-p) := by
  have hk := PrimitiveSocleBelowTwentyFiveSingleFactorWithoutIndexInput.factorCount_eq_one D hsmall
  have hcard : Nat.card (finiteGroupSocle G)=Nat.card D.Simple :=
    Nat.card_congr (D.oneFactorEquiv hk).toEquiv
  have hQ := quotient_genRank_le_fixedBudget (p := p) (X := X) hclass (finiteGroupSocle G)
    (by rw [hcard]; exact hpdiv) (by rw [hcard]; exact hnot) hdegree hfixed
  have hG := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_actual_quotient D hk
  omega
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.LargePrimeSocleQuotientGenerators

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleLargePrimePairBoundedSharp
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleLargePrimePairBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics
open _root_.SymmetricSubgroupAsymptotics.TenPointHalfDegreeCompleteCFSG (fixedBudget)

private theorem fixed_budget_pays (n p : ℕ) (hlo : 11 ≤ n) (hhi : n ≤ 21) (hp : 11 ≤ p) :
    3+fixedBudget (n-p) ≤ sharpFloor n := by
  by_cases h16 : n ≤ 16
  · have hb : fixedBudget (n-p) ≤ 2 := by unfold fixedBudget; split_ifs <;> omega
    exact (by omega : 3+fixedBudget (n-p) ≤ 5).trans
      (_root_.SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction.five_le_sharpFloor_of_band n hlo hhi)
  by_cases h18 : n ≤ 18
  · have hb : fixedBudget (n-p) ≤ 3 := by unfold fixedBudget; split_ifs <;> omega
    exact (by omega : 3+fixedBudget (n-p) ≤ 6).trans
      (_root_.SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedSharpCFSGReduction.six_le_sharpFloor_of_band n (by omega) hhi)
  by_cases h20 : n ≤ 20
  · have hb : fixedBudget (n-p) ≤ 4 := by unfold fixedBudget; split_ifs <;> omega
    have hseven : 7 ≤ sharpFloor n :=
      TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square n 7 5 (by omega)
        (TinyPrimeTopSharpFloorNumerics.log_le_of_pow n 5 (by omega) (by norm_num; omega))
        (by
          have hh := Nat.pow_le_pow_left (show 19 ≤ n by omega) 2
          norm_num at hh ⊢
          omega)
    exact (by omega : 3+fixedBudget (n-p) ≤ 7).trans hseven
  · have hn : n=21 := by omega
    have hb : fixedBudget (n-p) ≤ 5 := by unfold fixedBudget; split_ifs <;> omega
    exact (by omega : 3+fixedBudget (n-p) ≤ 8).trans
      (by simpa only [hn] using TinyPrimeTopSharpFloorNumerics.eight_le_sharpFloor_twenty_one)


theorem genRank_le_sharpFloor_of_prime
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : Nat.card X ≤ 21)
    (p : ℕ) (hp : p.Prime) (hplo : 11 ≤ p) (hpdiv : p ∣ Nat.card D.Simple)
    (hhead : MarkedC4.genRank D.Simple ≤ 2) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  have hple : p ≤ Nat.card X := hp.dvd_factorial.mp (hpdiv.trans hd)
  have hnot : ¬p^2 ∣ Nat.card D.Simple := by
    have htable : ∀ q : Fin 22, q.val.Prime → 11 ≤ q.val → ¬q.val^2 ∣ Nat.factorial 21 := by
      decide +kernel
    intro hh
    exact htable ⟨p,by omega⟩ hp hplo
      (hh.trans (hd.trans (Nat.factorial_dvd_factorial hhi)))
  have hb := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.LargePrimeSocleQuotientGenerators.nonaffine_genRank_le_fixedBudget
    (p := p) (X := X) hclass D (by omega) hhead hpdiv hnot (by omega) (by omega)
  exact hb.trans (fixed_budget_pays (Nat.card X) p (by omega) hhi hplo)

theorem genRank_le_sharpFloor_of_model
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : Nat.card X ≤ 21)
    (s : CFSG.Sporadic) (hs : LargePrimePairTag s) (e : D.Simple ≃* s.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  have hn : ¬IsMulCommutative s.Model := fun hc =>
    D.noncommutative ((isMulCommutative_congr e).mpr hc)
  obtain ⟨hp,hplo,hpdiv⟩ := model_prime s hs hn
  have hd : selectedPrime s ∣ Nat.card D.Simple := by
    rw [Nat.card_congr e.toEquiv]
    exact hpdiv
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm (model_pair s hs)
  exact genRank_le_sharpFloor_of_prime D hclass hhi (selectedPrime s) hp hplo hd
    ((MarkedC4.genRank_le hS).trans hcard)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleLargePrimePairBoundedSharp

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleCoOnePrimeElevenBoundedSharp
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleCoOnePrimeElevenBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics

attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.Co1.rows1
  CFSG.Models.MatrixGroups.Co1.rows2

private theorem pair_head_transport {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (hpair : CFSGGeneration.TwoGenerated B) : MarkedC4.genRank A ≤ 2 := by
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm hpair
  exact (MarkedC4.genRank_le hS).trans hcard

set_option maxRecDepth 4096 in
theorem genRank_le_sharpFloor_of_coOne
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Co1.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  have hhead : MarkedC4.genRank D.Simple ≤ 2 :=
    @pair_head_transport D.Simple CFSG.Models.MatrixGroups.Co1.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Co1.Model) e CFSGGeneration.co1_twoGenerated
  exact _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_prime
    D hclass hhi 11 (by decide) (by decide) (simple_eleven_dvd D e) hhead
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleCoOnePrimeElevenBoundedSharp

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointFaithfulActionHalfDegreeReduction
open _root_.SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction

theorem two_mul_genRank_le_card_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) {G X : Type}
    [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (hsmall : Nat.card X ≤ 8) (hthree : Nat.card X ≠ 3) :
    2*MarkedC4.genRank G ≤ Nat.card X ∨
      Nonempty (PrimitiveSporadicCounterexample 8) := by
  let e : X ≃ Fin (Nat.card X) := Finite.equivFinOfCardEq rfl
  let rho : G →* Equiv.Perm (Fin (Nat.card X)) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have hrho : Function.Injective rho :=
    e.permCongrHom.injective.comp MulAction.toPerm_injective
  let f : G ≃* rho.range := MonoidHom.ofInjective hrho
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointHalfDegreeFiniteModelReduction.half_degree_or_sporadic_counterexample
    hclass (Nat.card X) hsmall rho.range (fun h => (hthree h).elim) with hpaid | hbad
  · exact Or.inl (by
      simpa only [← CoprimeNilpotentProductGenerators.genRank_mulEquiv f] using hpaid)
  · exact Or.inr (counterexample_mono hsmall hbad)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointFaithfulActionHalfDegreeReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineNineBoundedSharpStep
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineNineBoundedSharpStep
open OddPrimePowerAffineBlockCoordinates OddPrimePowerAffineBlockPairCompression
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction TraceySharpHalfDegreeNumerics

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.1; omega)
local instance pointsNontrivial : Nontrivial block.Points :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.2; omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hr : Nat.card block.Fibre = 9) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  let b := block.map
  let hb := block.map_equivariant
  let C := P.elementaryChart block.component_preprimitive
  let origin : block.Fibre := ⟨x₀,block.map_base⟩
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_equiv P.V
    (C.equiv.toEquiv.trans (Multiplicative.toAdd : Multiplicative C.V ≃ C.V))
  have hproduct : 9*Nat.card block.Points = n := by
    simpa only [hr,Nat.card_fin] using block.degree_product
  have ht : Nat.card block.Points = 2 := by
    have hh := block.degrees_ge_two.2
    omega
  have hn : n = 18 := by omega
  have hpow : P.p^C.d = 9 := by
    have he := P.degree_eq_prime_pow_finrank C.equiv origin
    simpa only [PrimitiveAffineProfile.ElementaryChart.d,hr] using he.symm
  have hpdiv : P.p ∣ 3^2 := by
    change P.p ∣ 9
    rw [← hpow]
    exact dvd_pow_self _ C.d_pos.ne'
  have hp : P.p = 3 := Nat.prime_eq_prime_of_dvd_pow P.p_prime (by decide) hpdiv
  have hd : C.d = 2 := Nat.pow_right_injective (by decide : 2 ≤ 3)
    (by simpa only [hp] using hpow)
  have hfree : ∀ v : Multiplicative C.V, v ≠ 1 → v⁻¹ ≠ v := by
    intro v hv he
    have hnv : C.equiv.symm v ≠ 1 := by
      intro h
      apply hv
      simpa only [C.equiv.apply_symm_apply,map_one] using congrArg C.equiv h
    have he' : (C.equiv.symm v)⁻¹ = C.equiv.symm v :=
      (map_inv C.equiv.symm v).symm.trans (congrArg C.equiv.symm he)
    exact PrimitiveAffineOddOrdinaryInduction.translation_inverse_ne_self P (by omega) _ hnv he'
  have hcard : Nat.card (Multiplicative C.V) = 9 :=
    (Nat.card_congr C.equiv).symm.trans ((P.card_eq origin).trans hr)
  have hpairs : 2*Nat.card (Pairs b hb block.base P block.component_preprimitive C) ≤ 8 := by
    have hh := AbelianAutomorphismInversionPairs.two_mul_pairCard_le (V := Multiplicative C.V) hfree
    simpa only [hcard] using hh
  obtain ⟨v,hv⟩ := exists_ne (1 : Multiplicative C.V)
  letI : Nonempty (Pairs b hb block.base P block.component_preprimitive C) :=
    ⟨FreeInvolutionPairQuotient.mk
      (AbelianAutomorphismInversionPairs.inversion (Multiplicative C.V))
      (AbelianAutomorphismInversionPairs.inversion_involutive (Multiplicative C.V)) ⟨v,hv⟩⟩
  let E := pairKernel b hb block.base P block.component_preprimitive C origin
  let Y := Pairs b hb block.base P block.component_preprimitive C × block.Points
  have hY : Nat.card Y ≤ 8 := by
    change Nat.card (Pairs b hb block.base P block.component_preprimitive C × block.Points) ≤ 8
    rw [Nat.card_prod,ht]
    omega
  have hthree : Nat.card Y ≠ 3 := by
    change Nat.card (Pairs b hb block.base P block.component_preprimitive C × block.Points) ≠ 3
    rw [Nat.card_prod,ht]
    omega
  letI : MulAction (LinearQuotient b hb block.base P origin ⧸ E) Y :=
    MulAction.compHom Y (quotientAction b hb block.base P block.component_preprimitive C origin)
  letI : FaithfulSMul (LinearQuotient b hb block.base P origin ⧸ E) Y := by
    constructor
    intro u w he
    apply quotientAction_injective b hb block.base P block.component_preprimitive C origin
    exact Equiv.ext he
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointFaithfulActionHalfDegreeReduction.two_mul_genRank_le_card_or_sporadic_counterexample
    hclass (G := LinearQuotient b hb block.base P origin ⧸ E) (X := Y) hY hthree with hpaid | hbad
  · have hquot : MarkedC4.genRank (LinearQuotient b hb block.base P origin ⧸ E) ≤ 4 := by omega
    have hgen := OddAffinePairQuotientOrdinaryRank.genRank_le_pairQuotient_add_dimension_mul_half
      b hb block.base P block.component_preprimitive C origin
    change MarkedC4.genRank J ≤
      MarkedC4.genRank (LinearQuotient b hb block.base P origin ⧸ E) + (C.d+1)*(Nat.card block.Points/2) at hgen
    have hg : MarkedC4.genRank J ≤ 7 := by rw [hd,ht] at hgen; omega
    exact Or.inl (hg.trans (by simpa only [hn] using
      _root_.SymmetricSubgroupAsymptotics.OriginalTernaryBoundedSharpStep.seven_le_sharpFloor_eighteen))
  · exact Or.inr hbad
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineNineBoundedSharpStep

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalBinaryBoundedSharpStep
open _root_.SymmetricSubgroupAsymptotics.OriginalBinaryBoundedSharpStep
open OriginalBlockOrdinaryCompressionState TraceySharpHalfDegreeNumerics
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction FiniteGroupPrimeMultiplicityGenerators

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

private theorem component_card_dvd_two (hr : Nat.card block.Fibre = 2) :
    Nat.card block.Component ∣ 2 := by
  letI : Fintype block.Fibre := Fintype.ofFinite _
  have hd := Subgroup.card_dvd_of_injective block.Component.subtype block.Component.subtype_injective
  have hperm : Nat.card (Equiv.Perm block.Fibre) = 2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_eq_nat_card,hr]
    norm_num
  simpa only [hperm] using hd

private theorem top_rank_or_sporadic_counterexample (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (ht : Nat.card block.Points ≤ 10) :
    MarkedC4.genRank block.Top ≤ Nat.card block.Points/2 +
      (if Nat.card block.Points = 3 then 1 else 0) ∨
        Nonempty (PrimitiveSporadicCounterexample 10) := by
  by_cases hthree : Nat.card block.Points = 3
  · have hcard : Nat.card block.Top ≤ 6 := by
      have hh := Nat.card_le_card_of_injective
        (MulAction.toPermHom block.Top block.Points) MulAction.toPerm_injective
      simpa only [Nat.card_perm,hthree,Nat.factorial_succ,Nat.factorial_zero] using hh
    have htop : MarkedC4.genRank block.Top ≤ 2 := by
      by_contra hh
      have hg : 3 ≤ MarkedC4.genRank block.Top := by omega
      have hp := (Nat.pow_le_pow_right (by decide : 0 < 2) hg).trans
        ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card block.Top).trans hcard)
      norm_num at hp
    exact Or.inl (by norm_num only [hthree]; exact htop)
  · rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointHalfDegreeFiniteModelReduction.two_mul_genRank_le_card_or_sporadic_counterexample
      hclass (G := block.Top) (X := block.Points) ht hthree with hp | hbad
    · exact Or.inl (by simp only [if_neg hthree]; omega)
    · exact Or.inr hbad

theorem genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hr : Nat.card block.Fibre = 2) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ n = 16 ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  by_cases h16 : n = 16
  · exact Or.inr (Or.inl h16)
  have hproduct : 2*Nat.card block.Points = n := by
    simpa only [hr,Nat.card_fin] using block.degree_product
  have ht2 := block.degrees_ge_two.2
  have ht10 : Nat.card block.Points ≤ 10 := by omega
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using ht2
  have horder := component_card_dvd_two J block hr
  have hOmega : ArithmeticFunction.cardFactors (Nat.card block.Component) ≤ 1 :=
    (cardFactors_mono_of_dvd (Nat.card_pos (α := block.Component)).ne'
      (by decide : (2 : ℕ) ≠ 0) horder).trans_eq (by decide +kernel)
  have hbase := ActualWreathSharpUniformLocalOrderCost.genRank_le_half_local_cardFactors
    (initialState J block) block.base hI
  change (MarkedC4.genRank J : ℝ) ≤
    (ArithmeticFunction.cardFactors (Nat.card block.Component) : ℝ)*(Fintype.card block.Points : ℝ)/2+
      MarkedC4.genRank block.Top at hbase
  have hm : (ArithmeticFunction.cardFactors (Nat.card block.Component) : ℝ)*
      ((Fintype.card block.Points : ℝ)/2) ≤ (Fintype.card block.Points : ℝ)/2 := by
    have hh := mul_le_mul_of_nonneg_right
      (show (ArithmeticFunction.cardFactors (Nat.card block.Component) : ℝ) ≤ 1 by exact_mod_cast hOmega)
      (show (0 : ℝ) ≤ (Fintype.card block.Points : ℝ)/2 by positivity)
    simpa only [one_mul] using hh
  have hhalf : MarkedC4.genRank J ≤ Nat.card block.Points/2+MarkedC4.genRank block.Top := by
    have hhR : (2 : ℝ)*MarkedC4.genRank J ≤
        (Fintype.card block.Points : ℝ)+2*MarkedC4.genRank block.Top := by linarith only [hbase,hm]
    have hhR' : (2 : ℝ)*MarkedC4.genRank J ≤
        (Nat.card block.Points : ℝ)+2*MarkedC4.genRank block.Top := by
      simpa only [Fintype.card_eq_nat_card] using hhR
    have hhN : 2*MarkedC4.genRank J ≤ Nat.card block.Points+2*MarkedC4.genRank block.Top := by
      exact_mod_cast hhR'
    omega
  rcases top_rank_or_sporadic_counterexample J block hclass ht10 with htop | hbad
  swap
  · exact Or.inr (Or.inr hbad)
  apply Or.inl
  by_cases hspecial : Nat.card block.Points = 6 ∨ Nat.card block.Points = 9 ∨ Nat.card block.Points = 10
  · rcases hspecial with ht | ht | ht
    · have hd : 3^1 ∣ Fintype.card block.Points := by norm_num only [Fintype.card_eq_nat_card,ht]
      have hh := ActualWreathPrimeOrderCoprimeDivisorBudget.genRank_le_primeTo_divisor_add_top
        (initialState J block) block.base hI 2 3 1 Nat.prime_two Nat.prime_three (by decide) horder hd
      change (MarkedC4.genRank J : ℝ) ≤ _+MarkedC4.genRank block.Top at hh
      norm_num only [Fintype.card_eq_nat_card,ht] at hh
      have htopN : MarkedC4.genRank block.Top ≤ 3 := by
        have h := htop; norm_num only [ht] at h; exact h
      have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ 3 := by exact_mod_cast htopN
      have hg : MarkedC4.genRank J ≤ 5 := by exact_mod_cast (show (MarkedC4.genRank J : ℝ) ≤ 5 by linarith)
      have hn : n = 12 := by omega
      exact hg.trans (by simpa only [hn] using TinyPrimeTopSharpFloorNumerics.five_le_sharpFloor_twelve)
    · have hd : 3^2 ∣ Fintype.card block.Points := by norm_num only [Fintype.card_eq_nat_card,ht]
      have hh := ActualWreathPrimeOrderCoprimeDivisorBudget.genRank_le_primeTo_divisor_add_top
        (initialState J block) block.base hI 2 3 2 Nat.prime_two Nat.prime_three (by decide) horder hd
      change (MarkedC4.genRank J : ℝ) ≤ _+MarkedC4.genRank block.Top at hh
      norm_num only [Fintype.card_eq_nat_card,ht] at hh
      have htopN : MarkedC4.genRank block.Top ≤ 4 := by
        have h := htop; norm_num only [ht] at h; exact h
      have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ 4 := by exact_mod_cast htopN
      have hg : MarkedC4.genRank J ≤ 5 := by exact_mod_cast (show (MarkedC4.genRank J : ℝ) ≤ 5 by linarith)
      have hn : n = 18 := by omega
      exact hg.trans ((by decide : 5 ≤ 7).trans (by simpa only [hn] using
        _root_.SymmetricSubgroupAsymptotics.OriginalTernaryBoundedSharpStep.seven_le_sharpFloor_eighteen))
    · have hd : 5^1 ∣ Fintype.card block.Points := by norm_num only [Fintype.card_eq_nat_card,ht]
      have hh := ActualWreathPrimeOrderCoprimeDivisorBudget.genRank_le_primeTo_divisor_add_top
        (initialState J block) block.base hI 2 5 1 Nat.prime_two (by decide) (by decide) horder hd
      change (MarkedC4.genRank J : ℝ) ≤ _+MarkedC4.genRank block.Top at hh
      norm_num only [Fintype.card_eq_nat_card,ht] at hh
      have htopN : MarkedC4.genRank block.Top ≤ 5 := by
        have h := htop; norm_num only [ht] at h; exact h
      have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ 5 := by exact_mod_cast htopN
      have hg : MarkedC4.genRank J ≤ 7 := by exact_mod_cast (show (MarkedC4.genRank J : ℝ) ≤ 7 by linarith)
      have hn : n = 20 := by omega
      exact hg.trans ((by decide : 7 ≤ 8).trans (by simpa only [hn] using
        SmallPrimeTopSharpFloorCertificates.eight_le_sharpFloor_twenty))
  have hcases : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 5 ∨ Nat.card block.Points = 7 := by omega
  rcases hcases with ht | ht | ht | ht | ht
  · have hg : MarkedC4.genRank J ≤ 2 := by norm_num only [ht,if_true,if_false] at hhalf htop; omega
    have hn : n = 4 := by omega
    exact hg.trans (by simpa only [hn] using _root_.SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpCFSGReduction.two_le_sharpFloor_four)
  · have hg : MarkedC4.genRank J ≤ 3 := by norm_num only [ht,if_true,if_false] at hhalf htop; omega
    have hn : n = 6 := by omega
    exact hg.trans (by simpa only [hn] using _root_.SymmetricSubgroupAsymptotics.OriginalTernaryBoundedSharpStep.three_le_sharpFloor_six)
  · have hg : MarkedC4.genRank J ≤ 4 := by norm_num only [ht,if_true,if_false] at hhalf htop; omega
    have hn : n = 8 := by omega
    have hf8 : 4 ≤ sharpFloor 8 := TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square
      8 4 3 (by decide) (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 8 3 (by decide) (by decide)) (by decide)
    exact hg.trans (by simpa only [hn] using hf8)
  · have hg : MarkedC4.genRank J ≤ 4 := by norm_num only [ht,if_true,if_false] at hhalf htop; omega
    have hn : n = 10 := by omega
    exact hg.trans (by simpa only [hn] using SmallPrimeTopSharpFloorCertificates.four_le_sharpFloor_ten)
  · have hg : MarkedC4.genRank J ≤ 6 := by norm_num only [ht,if_true,if_false] at hhalf htop; omega
    have hn : n = 14 := by omega
    exact hg.trans (_root_.SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedSharpCFSGReduction.six_le_sharpFloor_of_band n (by omega) (by omega))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalBinaryBoundedSharpStep

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalFourPointBoundedSharpStep
open _root_.SymmetricSubgroupAsymptotics.OriginalFourPointBoundedSharpStep
open OriginalBlockOrdinaryCompressionState OriginalAffineBlockCharacteristicHead
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction TraceySharpHalfDegreeNumerics
open FiniteGroupPrimeMultiplicityGenerators

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.1; omega)
variable (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hfour : Nat.card block.Fibre = 4) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ n = 16 ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  by_cases h16 : n = 16
  · exact Or.inr (Or.inl h16)
  have hproduct : 4*Nat.card block.Points = n := by
    simpa only [hfour,Nat.card_fin] using block.degree_product
  have ht2 := block.degrees_ge_two.2
  have ht5 : Nat.card block.Points ≤ 5 := by omega
  have hcases : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨ Nat.card block.Points = 5 := by omega
  rcases hcases with ht | ht | ht
  · have hn : n = 8 := by omega
    rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointFaithfulActionHalfDegreeReduction.two_mul_genRank_le_card_or_sporadic_counterexample
      hclass (G := J) (X := Fin n)
      (by simpa only [Nat.card_fin,hn] using (show 8 ≤ 8 by decide))
      (by simpa only [Nat.card_fin,hn] using (show (8 : ℕ) ≠ 3 by decide)) with hpaid | hbad
    · have hg : MarkedC4.genRank J ≤ 4 := by simp only [Nat.card_fin] at hpaid; omega
      have hf8 : 4 ≤ sharpFloor 8 := TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square
        8 4 3 (by decide) (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 8 3 (by decide) (by decide)) (by decide)
      exact Or.inl (hg.trans (by simpa only [hn] using hf8))
    · exact Or.inr (Or.inr (_root_.SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction.counterexample_mono (by decide : 8 ≤ 10) hbad))
  · have hn : n = 12 := by omega
    have hprime : (Fintype.card block.Points).Prime := by rw [Fintype.card_eq_nat_card,ht]; decide
    have htopcard : Nat.card block.Top ≤ 6 := by
      have hh := Nat.card_le_card_of_injective
        (MulAction.toPermHom block.Top block.Points) MulAction.toPerm_injective
      simpa only [Nat.card_perm,ht,Nat.factorial_succ,Nat.factorial_zero] using hh
    have htop : MarkedC4.genRank block.Top ≤ 2 := by
      by_contra hh
      have hg : 3 ≤ MarkedC4.genRank block.Top := by omega
      have hp := (Nat.pow_le_pow_right (by decide : 0 < 2) hg).trans
        ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card block.Top).trans htopcard)
      norm_num at hp
    have hdpos : 0 < translationDimension J block P :=
      (P.elementaryChart block.component_preprimitive).d_pos
    have hpow : P.p^translationDimension J block P = 4 :=
      (fibre_card_eq_prime_pow_dimension J block P).symm.trans hfour
    have hpdiv : P.p ∣ 2^2 := by
      change P.p ∣ 4
      rw [← hpow]
      exact dvd_pow_self _ hdpos.ne'
    have hp : P.p = 2 := Nat.prime_eq_prime_of_dvd_pow P.p_prime Nat.prime_two hpdiv
    have hd : translationDimension J block P = 2 := Nat.pow_right_injective (by decide : 2 ≤ 2)
      (by simpa only [hp] using hpow)
    have hg : MarkedC4.genRank J ≤ 5 := by
      by_cases hzero : BinaryPlaneWreathActualOddKernel.oddKernel
          (FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour) = ⊥
      · have hcapacity := ActualWreathPrimeTopChiefOrdinaryBudget.elementary_capacity_le_dimension
          (initialState J block) (QuotientGroup.mk' P.V) (translationChart J block P) block.base hprime
        change (headCharge J block P block.base).capacity ≤ translationDimension J block P at hcapacity
        have hgen := OriginalFourPointZeroOddCharacteristicCost.genRank_le_head_add_top
          J block P hfour hp hzero block.base
        omega
      · have horder := OriginalFourPointSharedChooseCost.quotientState_card_dvd_six J block P hp hd
        have hOmega : ArithmeticFunction.cardFactors (Nat.card (quotientState J block P).D) ≤ 2 :=
          (cardFactors_mono_of_dvd (Nat.card_pos (α := (quotientState J block P).D)).ne'
            (by decide : (6 : ℕ) ≠ 0) horder).trans_eq (by decide +kernel)
        have htail := ActualWreathPrimeTopChiefOrdinaryBudget.genRank_le_cardFactors_add_top
          (quotientState J block P) block.base hprime
        have hhead := OriginalFourPointSharedTranslationKernel.genRank_le_half_add_quotient
          J block P hfour hp hzero
        norm_num only [ht] at hhead
        omega
    exact Or.inl (hg.trans (by simpa only [hn] using TinyPrimeTopSharpFloorNumerics.five_le_sharpFloor_twelve))
  · have hn : n = 20 := by omega
    have hdiv : Nat.card block.Component ∣ 24 := by
      letI : Fintype block.Fibre := Fintype.ofFinite _
      have hh := Subgroup.card_dvd_of_injective block.Component.subtype block.Component.subtype_injective
      have he : Nat.card (Equiv.Perm block.Fibre) = 24 := by
        rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_eq_nat_card,hfour]
        norm_num
      simpa only [he] using hh
    have hOmega : ArithmeticFunction.cardFactors (Nat.card block.Component) ≤ 4 :=
      (cardFactors_mono_of_dvd (Nat.card_pos (α := block.Component)).ne'
        (by decide : (24 : ℕ) ≠ 0) hdiv).trans_eq (by decide +kernel)
    have hprime : (Fintype.card block.Points).Prime := by rw [Fintype.card_eq_nat_card,ht]; decide
    have hsource := ActualWreathPrimeTopChiefOrdinaryBudget.genRank_le_cardFactors_add_top
      (initialState J block) block.base hprime
    change MarkedC4.genRank J ≤ ArithmeticFunction.cardFactors (Nat.card block.Component) +
      MarkedC4.genRank block.Top at hsource
    rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointFaithfulActionHalfDegreeReduction.two_mul_genRank_le_card_or_sporadic_counterexample
      hclass (G := block.Top) (X := block.Points) (by omega) (by omega) with htop | hbad
    · have hg : MarkedC4.genRank J ≤ 6 := by omega
      exact Or.inl (hg.trans ((by decide : 6 ≤ 8).trans (by simpa only [hn] using
        SmallPrimeTopSharpFloorCertificates.eight_le_sharpFloor_twenty)))
    · exact Or.inr (Or.inr (_root_.SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction.counterexample_mono (by decide : 8 ≤ 10) hbad))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalFourPointBoundedSharpStep

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalFourPointCompleteBoundedSharpStep
open _root_.SymmetricSubgroupAsymptotics.OriginalFourPointCompleteBoundedSharpStep
open TraceySharpHalfDegreeNumerics _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hfour : Nat.card block.Fibre = 4) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalFourPointBoundedSharpStep.genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample
    J block P hclass hfour hsmall with hpaid | h16 | hbad
  · exact Or.inl hpaid
  · exact Or.inl (OriginalFourPointSixteenSharpStep.genRank_le_sharpFloor J block P hfour h16)
  · exact Or.inr hbad
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalFourPointCompleteBoundedSharpStep

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalTernaryBoundedSharpStep
open _root_.SymmetricSubgroupAsymptotics.OriginalTernaryBoundedSharpStep
open OriginalBlockOrdinaryCompressionState TraceySharpHalfDegreeNumerics
open ActualWreathChooseDivisorCapacity _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction
open FiniteGroupPrimeMultiplicityGenerators

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

private theorem top_rank_or_sporadic_counterexample (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (ht : Nat.card block.Points ≤ 7) :
    MarkedC4.genRank block.Top ≤ Nat.card block.Points/2 +
      (if Nat.card block.Points = 3 then 1 else 0) ∨
        Nonempty (PrimitiveSporadicCounterexample 8) := by
  by_cases hthree : Nat.card block.Points = 3
  · have hcard : Nat.card block.Top ≤ 6 := by
      have hh := Nat.card_le_card_of_injective
        (MulAction.toPermHom block.Top block.Points) MulAction.toPerm_injective
      simpa only [Nat.card_perm,hthree,Nat.factorial_succ,Nat.factorial_zero] using hh
    have htop : MarkedC4.genRank block.Top ≤ 2 := by
      by_contra hh
      have hg : 3 ≤ MarkedC4.genRank block.Top := by omega
      have hp := (Nat.pow_le_pow_right (by decide : 0 < 2) hg).trans
        ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card block.Top).trans hcard)
      norm_num at hp
    exact Or.inl (by norm_num only [hthree]; exact htop)
  · rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointFaithfulActionHalfDegreeReduction.two_mul_genRank_le_card_or_sporadic_counterexample
      hclass (G := block.Top) (X := block.Points) (by omega) hthree with hp | hbad
    · exact Or.inl (by simp only [if_neg hthree]; omega)
    · exact Or.inr hbad

theorem genRank_le_sharpFloor_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hr : Nat.card block.Fibre = 3) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  have hproduct : 3*Nat.card block.Points = n := by
    simpa only [hr,Nat.card_fin] using block.degree_product
  have ht2 := block.degrees_ge_two.2
  have ht7 : Nat.card block.Points ≤ 7 := by omega
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using ht2
  have horder := OriginalTernaryCoarseOrdinaryStep.component_card_dvd_six J block hr
  have hOmega : ArithmeticFunction.cardFactors (Nat.card block.Component) ≤ 2 :=
    (cardFactors_mono_of_dvd (Nat.card_pos (α := block.Component)).ne'
      (by decide : (6 : ℕ) ≠ 0) horder).trans_eq (by decide +kernel)
  rcases top_rank_or_sporadic_counterexample J block hclass ht7 with htop | hbad
  swap
  · exact Or.inr hbad
  apply Or.inl
  by_cases ht4 : Nat.card block.Points = 4
  · have hdiv : 2^2 ∣ Fintype.card block.Points := by
      norm_num only [Fintype.card_eq_nat_card,ht4]
    have hh := ActualWreathSixOrderChooseCost.genRank_le_primary_choose_add_primeTo
      (initialState J block) block.base hI horder 2 hdiv
    change (MarkedC4.genRank J : ℝ) ≤ _ + _ + MarkedC4.genRank block.Top at hh
    norm_num only [Fintype.card_eq_nat_card,ht4,primaryRate,Nat.choose,min_def] at hh
    have htopN : MarkedC4.genRank block.Top ≤ 2 := by
      have hh := htop
      norm_num only [ht4] at hh
      exact hh
    have htopR : (MarkedC4.genRank block.Top : ℝ) ≤ 2 := by exact_mod_cast htopN
    have hg : MarkedC4.genRank J ≤ 5 := by exact_mod_cast (show (MarkedC4.genRank J : ℝ) ≤ 5 by linarith)
    have hn : n = 12 := by omega
    exact hg.trans (by simpa only [hn] using TinyPrimeTopSharpFloorNumerics.five_le_sharpFloor_twelve)
  by_cases ht6 : Nat.card block.Points = 6
  · have htF : Fintype.card block.Points = 6 := by
      simpa only [Fintype.card_eq_nat_card] using ht6
    have hh := ActualWreathSixTopChiefOrdinaryBudget.genRank_le_four_add_top_of_card_dvd_six
      (initialState J block) block.base htF horder
    change MarkedC4.genRank J ≤ 4+MarkedC4.genRank block.Top at hh
    have htopN : MarkedC4.genRank block.Top ≤ 3 := by
      have h := htop
      norm_num only [ht6] at h
      exact h
    have hg : MarkedC4.genRank J ≤ 7 := by omega
    have hn : n = 18 := by omega
    exact hg.trans (by simpa only [hn] using seven_le_sharpFloor_eighteen)
  have hcases : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 5 ∨ Nat.card block.Points = 7 := by omega
  have hprime : (Fintype.card block.Points).Prime := by
    rw [Fintype.card_eq_nat_card]
    rcases hcases with ht | ht | ht | ht <;> rw [ht] <;> decide
  have hh := ActualWreathPrimeTopChiefOrdinaryBudget.genRank_le_cardFactors_add_top
    (initialState J block) block.base hprime
  change MarkedC4.genRank J ≤ ArithmeticFunction.cardFactors (Nat.card block.Component) +
    MarkedC4.genRank block.Top at hh
  rcases hcases with ht | ht | ht | ht
  · have htopN : MarkedC4.genRank block.Top ≤ 1 := by
      have hh := htop
      norm_num only [ht] at hh
      exact hh
    have hg : MarkedC4.genRank J ≤ 3 := by omega
    have hn : n = 6 := by omega
    exact hg.trans (by simpa only [hn] using three_le_sharpFloor_six)
  · have htopN : MarkedC4.genRank block.Top ≤ 2 := by
      have hh := htop
      norm_num only [ht] at hh
      exact hh
    have hg : MarkedC4.genRank J ≤ 4 := by omega
    have hn : n = 9 := by omega
    exact hg.trans (by simpa only [hn] using PrimitiveAffineNineOrdinaryGenerators.four_le_sharpFloor_nine)
  · have htopN : MarkedC4.genRank block.Top ≤ 2 := by
      have hh := htop
      norm_num only [ht] at hh
      exact hh
    have hg : MarkedC4.genRank J ≤ 4 := by omega
    have hn : n = 15 := by omega
    exact hg.trans ((by decide : 4 ≤ 6).trans (by simpa only [hn] using
      TinyPrimeTopSharpFloorNumerics.six_le_sharpFloor_fifteen))
  · have htopN : MarkedC4.genRank block.Top ≤ 3 := by
      have hh := htop
      norm_num only [ht] at hh
      exact hh
    have hg : MarkedC4.genRank J ≤ 5 := by omega
    have hn : n = 21 := by omega
    exact hg.trans ((by decide : 5 ≤ 8).trans (by simpa only [hn] using
      TinyPrimeTopSharpFloorNumerics.eight_le_sharpFloor_twenty_one))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalTernaryBoundedSharpStep

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpTwoFibreReduction
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpTwoFibreReduction
open TraceySharpHalfDegreeNumerics _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_two_fibres_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ (Nat.card block.Fibre = 2 ∨ Nat.card block.Fibre = 8)) ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases OriginalAffineBoundedSharpCFSGReduction.affine_fibre_cases J block P hsmall with
    h2 | h3 | h4 | h5 | h7 | h8 | h9
  · rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalBinaryBoundedSharpStep.genRank_le_sharpFloor_or_sixteen_or_sporadic_counterexample
      J block hclass h2 hsmall with hpaid | h16 | hbad
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl ⟨h16,Or.inl h2⟩)
    · exact Or.inr (Or.inr hbad)
  · rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalTernaryBoundedSharpStep.genRank_le_sharpFloor_or_sporadic_counterexample
      J block hclass h3 hsmall with hpaid | hbad
    · exact Or.inl hpaid
    · exact Or.inr (Or.inr (_root_.SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction.counterexample_mono
        (by decide : 8 ≤ 10) hbad))
  · rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalFourPointCompleteBoundedSharpStep.genRank_le_sharpFloor_or_sporadic_counterexample
      J block P hclass h4 hsmall with hpaid | hbad
    · exact Or.inl hpaid
    · exact Or.inr (Or.inr hbad)
  · exact Or.inl (OriginalAffineFiveSevenBoundedSharpStep.genRank_le_sharpFloor J block P (Or.inl h5) hsmall)
  · exact Or.inl (OriginalAffineFiveSevenBoundedSharpStep.genRank_le_sharpFloor J block P (Or.inr h7) hsmall)
  · have hproduct : 8*Nat.card block.Points = n := by
      simpa only [h8,Nat.card_fin] using block.degree_product
    have ht := block.degrees_ge_two.2
    exact Or.inr (Or.inl ⟨by omega,Or.inr h8⟩)
  · rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineNineBoundedSharpStep.genRank_le_sharpFloor_or_sporadic_counterexample
      J block P hclass h9 hsmall with hpaid | hbad
    · exact Or.inl hpaid
    · exact Or.inr (Or.inr (_root_.SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction.counterexample_mono
        (by decide : 8 ≤ 10) hbad))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpTwoFibreReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpBinaryFibreReduction
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpBinaryFibreReduction
open TraceySharpHalfDegreeNumerics _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_binary_sixteen_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nat.card block.Fibre = 2) ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpTwoFibreReduction.genRank_le_sharpFloor_or_two_fibres_or_sporadic_counterexample
    J block P hclass hsmall with
    hpaid | ⟨h16,h2 | h8⟩ | hbad
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl ⟨h16,h2⟩)
  · exact Or.inl (OriginalAffineEightTwoBlockSharpStep.genRank_le_sharpFloor J block P h8 h16)
  · exact Or.inr (Or.inr hbad)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpBinaryFibreReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSoclePairedDegreeEightOrdinary
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSoclePairedDegreeEightOrdinary
open PrimitiveSocleRawStructure PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X)

theorem genRank_le_three_or_actual_remaining_model (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (hdegree : Nat.card X = 8) (hnotSixteen : ¬16 ∣ Nat.card G) :
    MarkedC4.genRank G ≤ 3 ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases ExtendedCatalogueSmallDegreeModels.pair_family_or_actual_remaining_of_degree_below_twenty_four
    D hclass (by omega) with ⟨j,hj,⟨e⟩⟩ | hm
  · exact Or.inl (genRank_le_three_of_pair_family D j hj e hdegree hnotSixteen)
  · exact Or.inr hm
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSoclePairedDegreeEightOrdinary

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.ElementarySylowEightOrdinaryCFSGReduction
open _root_.SymmetricSubgroupAsymptotics.ElementarySylowEightOrdinaryCFSGReduction
open PrimitiveSocleRawStructure PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

variable (J : Subgroup (Equiv.Perm (Fin 8)))
    [MulAction.IsPretransitive J (Fin 8)]

theorem genRank_le_three_or_actual_sporadic (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (P : Sylow 2 J) (hel : ∀ g : P, g^2 = 1) :
    MarkedC4.genRank J ≤ 3 ∨ Nonempty (PrimitiveSporadicObstruction J P) := by
  by_cases hpaid : MarkedC4.genRank J ≤ 3
  · exact Or.inl hpaid
  have hnot16 : ¬16 ∣ Nat.card J :=
    ElementarySylowTransitiveOrderObstruction.sixteen_not_dvd_card_of_degree_eight
      (X := Fin 8) P hel (by simp only [Nat.card_fin])
  by_cases hprimitive : MulAction.IsPreprimitive J (Fin 8)
  · letI : MulAction.IsPreprimitive J (Fin 8) := hprimitive
    obtain ⟨D⟩ := publishedONanScottStructure J (Fin 8)
    cases D with
    | inr A =>
        have hh := A.subnormal_genRank_le_three_of_degreeEight hprimitive (0 : Fin 8)
          (by simp only [Nat.card_fin]) ⊤ (by exact Subgroup.Normal.isSubnormal inferInstance)
        rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv
          (Subgroup.topEquiv : (⊤ : Subgroup J) ≃* J)] at hh
        exact Or.inl hh
    | inl D =>
        rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSoclePairedDegreeEightOrdinary.genRank_le_three_or_actual_remaining_model
          D hclass (by simp only [Nat.card_fin]) hnot16 with hh | ⟨j,hj,⟨e⟩⟩
        · exact Or.inl hh
        · cases j <;> try exact hj.elim
          · exact (PrimitiveSocleElevenPointTitsExclusion.not_tits_of_degree_le_eleven
              D (by simp only [Nat.card_fin]; decide) e).elim
          · rename_i s
            exact Or.inr ⟨⟨hel,hnot16,hprimitive,by omega,D,s,e⟩⟩
  · obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) (0 : Fin 8) hprimitive
    letI : Fintype block.Points := Fintype.ofFinite _
    have hprod : Nat.card block.Fibre*Nat.card block.Points = 8 := by
      simpa only [Nat.card_fin] using block.degree_product
    obtain ⟨hr,ht⟩ := block.degrees_ge_two
    have hr4 : Nat.card block.Fibre ≤ 4 := by nlinarith only [hprod,ht]
    have hcases : Nat.card block.Fibre = 2 ∨ Nat.card block.Fibre = 4 := by
      have hthree : Nat.card block.Fibre ≠ 3 := by intro h; rw [h] at hprod; omega
      omega
    rcases hcases with h2 | h4
    · exact Or.inl (ElementarySylowEightBinaryBlockOrdinary.genRank_le_three J block P hel h2)
    · exact Or.inl (ElementarySylowEightTwoBlockOrdinary.genRank_le_three J block P hel h4)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.ElementarySylowEightOrdinaryCFSGReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.ElementarySylowEightFaithfulActionOrdinary
open _root_.SymmetricSubgroupAsymptotics.ElementarySylowEightFaithfulActionOrdinary
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

variable [MulAction.IsPretransitive G X]

theorem genRank_le_three_or_actual_sporadic (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (P : Sylow 2 G) (hel : ∀ g : P, g^2 = 1) (hcard : Nat.card X = 8) :
    MarkedC4.genRank G ≤ 3 ∨ Nonempty (ActualSporadicObstruction (G := G) (X := X)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : X ≃ Fin 8 := Finite.equivFinOfCardEq hcard
  let rho := relabelHom (G := G) e
  have hrho : Function.Injective rho :=
    e.permCongrHom.injective.comp MulAction.toPerm_injective
  let f : G ≃* rho.range := MonoidHom.ofInjective hrho
  let R : Sylow 2 rho.range := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have hR : ∀ r : R, r^2 = 1 := by
    intro r
    have hr : (r : rho.range) ∈ (P : Subgroup G).map f.toMonoidHom := r.property
    obtain ⟨g,hg,hgr⟩ := hr
    have hg2 : g^2 = 1 := congrArg (fun z : P => (z : G)) (hel ⟨g,hg⟩)
    apply Subtype.ext
    change (r : rho.range)^2 = 1
    rw [←hgr,←map_pow,hg2,map_one]
  letI : MulAction.IsPretransitive rho.range (Fin 8) := by
    constructor
    intro i j
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G (e.symm i) (e.symm j)
    refine ⟨rho.rangeRestrict g,?_⟩
    change e (g • e.symm i) = j
    simpa only [Equiv.apply_symm_apply] using congrArg e hg
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.ElementarySylowEightOrdinaryCFSGReduction.genRank_le_three_or_actual_sporadic
    rho.range hclass R hR with hh | hbad
  · exact Or.inl (by
      simpa only [←CoprimeNilpotentProductGenerators.genRank_mulEquiv f] using hh)
  · obtain ⟨w⟩ := hbad
    exact Or.inr ⟨⟨e,R,w⟩⟩
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.ElementarySylowEightFaithfulActionOrdinary

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalBinarySixteenSharpCFSGReduction
open _root_.SymmetricSubgroupAsymptotics.OriginalBinarySixteenSharpCFSGReduction
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction TraceySharpHalfDegreeNumerics

variable (J : Subgroup (Equiv.Perm (Fin 16)))
    [MulAction.IsPretransitive J (Fin 16)] {x₀ : Fin 16}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

theorem genRank_le_six_or_actual_top_sporadic_or_global_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hr : Nat.card block.Fibre = 2) :
    MarkedC4.genRank J ≤ 6 ∨
      Nonempty (_root_.SymmetricSubgroupAsymptotics.ElementarySylowEightFaithfulActionOrdinary.ActualSporadicObstruction
        (G := block.Top) (X := block.Points)) ∨
      Nonempty (PrimitiveSporadicCounterexample 8) := by
  have hprod : 2*Nat.card block.Points = 16 := by
    simpa only [hr,Nat.card_fin] using block.degree_product
  have ht : Nat.card block.Points = 8 := by omega
  letI : Nonempty block.Points := ⟨block.base⟩
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  have hrel : Nat.card block.Fibre = (MulAction.stabilizer J x₀).relIndex block.subgroup :=
    originalTransitiveBlockFibre_card x₀ block.subgroup block.covers.le
  let pair : TransitiveBinaryPairCover J x₀ :=
    ⟨block.subgroup,block.covers,hrel.symm.trans hr⟩
  let F := pair.frame
  have hact (g : J) (i : block.Points) : g • i = F.top g i := rfl
  by_cases hbinary : IsPGroup 2 block.Top
  · exact Or.inl (BinarySixteenTwoGroupSharpStep.genRank_le_six J
      (F.source_isPGroup_of_top_isPGroup hbinary) (by simp only [Nat.card_fin]))
  let Q : Sylow 2 block.Top := Classical.choice inferInstance
  by_cases hel : ∀ q : Q, q^2 = 1
  · rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.ElementarySylowEightFaithfulActionOrdinary.genRank_le_three_or_actual_sporadic
      hclass Q hel ht with htop | hbad
    · have hh := BinaryBlockCentralBinomialOrdinaryStep.genRank_le_top_add_middle
        F hact block.base 3 ht
      change MarkedC4.genRank J ≤ MarkedC4.genRank block.Top + 3 at hh
      exact Or.inl (by omega)
    · exact Or.inr (Or.inl hbad)
  have hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := Q) (X := block.Points) :=
    fun h => hel (BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mp h)
  have huTop := SylowNonelementaryPermutationQuarterGenerators.permutation_uniform
    Q 3 ht hnon
  have hu := UniformSubrepresentationGeneratorBound.comp_of_surjective
    (permutationFunctionRepresentation (ZMod 2) block.Top block.Points)
      block.topMap.rangeRestrict block.topMap.rangeRestrict_surjective huTop
  have he : (permutationFunctionRepresentation (ZMod 2) block.Top block.Points).comp
      block.topMap.rangeRestrict = permutationFunctionRepresentation (ZMod 2) J block.Points := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    funext i
    change v ((block.topMap g)⁻¹ i) = v (block.topMap (g⁻¹) i)
    rw [map_inv]
  rw [he] at hu
  have hu' : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) J block.Points) 2 := by
    simpa only [ht] using hu
  have hk := F.normalGen_le_of_uniform_pair_module hact 2 hu' F.top.ker le_rfl
  let pi : J →* F.top.range := F.top.rangeRestrict
  letI : IsMulCommutative pi.ker := by
    change IsMulCommutative F.top.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact BinaryBlockOrdinaryGeneratorInduction.kernel_isMulCommutative F
  have hk' : MarkedC4.normalGen pi.ker ≤ 2 := by
    change MarkedC4.normalGen F.top.rangeRestrict.ker ≤ 2
    rw [MonoidHom.ker_rangeRestrict]
    exact hk
  have hrec := (AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    pi F.top.rangeRestrict_surjective).trans (Nat.add_le_add_left hk' _)
  change MarkedC4.genRank J ≤ MarkedC4.genRank block.Top + 2 at hrec
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointFaithfulActionHalfDegreeReduction.two_mul_genRank_le_card_or_sporadic_counterexample
    hclass (G := block.Top) (X := block.Points) (by omega) (by omega) with hh | hbad
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr hbad)

theorem genRank_le_sharpFloor_or_actual_top_sporadic_or_global_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hr : Nat.card block.Fibre = 2) :
    MarkedC4.genRank J ≤ sharpFloor 16 ∨
      Nonempty (_root_.SymmetricSubgroupAsymptotics.ElementarySylowEightFaithfulActionOrdinary.ActualSporadicObstruction
        (G := block.Top) (X := block.Points)) ∨
      Nonempty (PrimitiveSporadicCounterexample 8) := by
  rcases genRank_le_six_or_actual_top_sporadic_or_global_counterexample J block hclass hr with
    hh | htop | hglobal
  · have hsix : 6 ≤ sharpFloor 16 := TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square
      16 6 4 (by decide)
        (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 16 4 (by decide) (by decide)) (by decide)
    exact Or.inl (hh.trans hsix)
  · exact Or.inr (Or.inl htop)
  · exact Or.inr (Or.inr hglobal)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalBinarySixteenSharpCFSGReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpSporadicReduction
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpSporadicReduction
open TraceySharpHalfDegreeNumerics _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_actual_top_sporadic_or_global_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty
        (_root_.SymmetricSubgroupAsymptotics.ElementarySylowEightFaithfulActionOrdinary.ActualSporadicObstruction
          (G := block.Top) (X := block.Points))) ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpBinaryFibreReduction.genRank_le_sharpFloor_or_binary_sixteen_or_sporadic_counterexample
      J block P hclass hsmall with hpaid | ⟨h16,h2⟩ | hbad
  · exact Or.inl hpaid
  · subst n
    rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalBinarySixteenSharpCFSGReduction.genRank_le_sharpFloor_or_actual_top_sporadic_or_global_counterexample
        J block hclass h2 with hpaid | htop | hglobal
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl ⟨rfl,htop⟩)
    · exact Or.inr (Or.inr (_root_.SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction.counterexample_mono
        (by decide : 8 ≤ 10) hglobal))
  · exact Or.inr (Or.inr hbad)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpSporadicReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpPrimeProductSporadicReduction
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpPrimeProductSporadicReduction
open TraceySharpHalfDegreeNumerics _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction
open CFSGSmallActionPrimeProductExclusion

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_refined_actual_top_or_refined_global
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (RefinedActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpSporadicReduction.genRank_le_sharpFloor_or_actual_top_sporadic_or_global_counterexample
    J block P hclass hsmall with hpaid | ⟨h16,htop⟩ | hglobal
  · exact Or.inl hpaid
  · obtain ⟨w⟩ := htop
    exact Or.inr (Or.inl ⟨h16,⟨refine_actual_top w⟩⟩)
  · obtain ⟨w⟩ := hglobal
    exact Or.inr (Or.inr ⟨refine_global (by decide : 10 ≤ 10) w⟩)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpPrimeProductSporadicReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpMathieuTopRefinement
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpMathieuTopRefinement
open TraceySharpHalfDegreeNumerics
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpPrimeProductSporadicReduction

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_mathieu_free_actual_top_or_refined_global
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (MathieuFreeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpPrimeProductSporadicReduction.genRank_le_sharpFloor_or_refined_actual_top_or_refined_global
    J block P hclass hsmall with hpaid | ⟨h16,htop⟩ | hglobal
  · exact Or.inl hpaid
  · obtain ⟨w⟩ := htop
    exact Or.inr (Or.inl ⟨h16,⟨refine_actual_top w⟩⟩)
  · exact Or.inr (Or.inr hglobal)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpMathieuTopRefinement

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open TraceySharpHalfDegreeNumerics
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpPrimeProductSporadicReduction
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpMathieuTopRefinement

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_co_two_free_actual_top_or_refined_global
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (CoTwoFreeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpMathieuTopRefinement.genRank_le_sharpFloor_or_mathieu_free_actual_top_or_refined_global
    J block P hclass hsmall with hpaid | ⟨h16,htop⟩ | hglobal
  · exact Or.inl hpaid
  · obtain ⟨w⟩ := htop
    exact Or.inr (Or.inl ⟨h16,⟨refine_actual_top w⟩⟩)
  · exact Or.inr (Or.inr hglobal)

include P in
theorem genRank_le_sharpFloor_or_cumulative_actual_top_or_refined_global
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (CumulativeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (RefinedGlobalCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_co_two_free_actual_top_or_refined_global
    J block P hclass hsmall with hpaid | ⟨h16,htop⟩ | hglobal
  · exact Or.inl hpaid
  · obtain ⟨w⟩ := htop
    exact Or.inr (Or.inl ⟨h16,⟨refine_actual_top_cumulative w⟩⟩)
  · exact Or.inr (Or.inr hglobal)

include P in
theorem genRank_le_sharpFloor_or_cumulative_sporadic_obstructions
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (CumulativeActualTopObstruction (G := block.Top) (X := block.Points))) ∨
      Nonempty (CumulativeGlobalCounterexample 10) := by
  rcases genRank_le_sharpFloor_or_cumulative_actual_top_or_refined_global
    J block P hclass hsmall with hpaid | htop | hglobal
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl htop)
  · obtain ⟨w⟩ := hglobal
    exact Or.inr (Or.inr ⟨refine_global_cumulative (by decide : 10 ≤ 10) w⟩)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpCoTwoTopRefinement

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalNonaffineBoundedSharpCFSGReduction
open _root_.SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedSharpCFSGReduction
open PrimitiveSocleRawStructure OriginalBlockOrdinaryCompressionState
open ActualWreathPrimitiveSocleOuterOrdinaryCost ActualWreathChiefUnitMinimumRate
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction TraceySharpHalfDegreeNumerics
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

variable (D : NonaffineData block.Component block.Fibre)

local instance stateComponentAction : MulAction (initialState J block).D block.Fibre :=
  inferInstanceAs (MulAction block.Component block.Fibre)

theorem genRank_le_sharpFloor_or_actual_remaining_model (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (hsmall : n < 22) : MarkedC4.genRank J ≤ sharpFloor n ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  have ht := block.degrees_ge_two.2
  have hproduct : Nat.card block.Fibre * Nat.card block.Points = n := by
    simpa only [Nat.card_fin] using block.degree_product
  have hr : Nat.card block.Fibre < 24 := by
    have hh := (Nat.mul_le_mul_left (Nat.card block.Fibre) ht).trans_eq hproduct
    omega
  rcases ExtendedCatalogueSmallDegreeModels.pair_family_or_actual_remaining_of_degree_below_twenty_four
    D hclass hr with ⟨j,hj,⟨e⟩⟩ | hm
  · exact Or.inl (genRank_le_sharpFloor_of_pair_family J block D j hj e hsmall)
  · exact Or.inr hm
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalNonaffineBoundedSharpCFSGReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveAffineSixteenEightPointSharpReduction
open _root_.SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenEightPointSharpReduction
open _root_.SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction TraceySharpHalfDegreeNumerics

theorem genRank_le_four_of_injective_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) {H : Type} [Group H] [Finite H]
    (f : H →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) (hf : Function.Injective f) :
    MarkedC4.genRank H ≤ 4 ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  let rho : H →* Equiv.Perm (Fin 8) := GeneralFourTwoAlternatingEquiv.eightAction.comp f
  have hrho : Function.Injective rho := GeneralFourTwoAlternatingEquiv.eightAction_injective.comp hf
  let e : H ≃* rho.range := MonoidHom.ofInjective hrho
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointHalfDegreeFiniteModelReduction.genRank_le_four_or_sporadic_counterexample
    hclass rho.range with hp | hbad
  · exact Or.inl ((CoprimeNilpotentProductGenerators.genRank_mulEquiv e).le.trans hp)
  · exact Or.inr hbad

private theorem complement_bound (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    {H : Type} [Group H] [Finite H] (p d : ℕ) [Fact p.Prime]
    (hp : p = 2) (hd : d = 4)
    (f : H →* Matrix.GeneralLinearGroup (Fin d) (ZMod p)) (hf : Function.Injective f) :
    MarkedC4.genRank H ≤ 4 ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  subst p
  subst d
  exact genRank_le_four_of_injective_or_sporadic_counterexample hclass f hf

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem genRank_le_five_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hprimitive : MulAction.IsPreprimitive G X)
    (hdegree : Nat.card X = 16) :
    MarkedC4.genRank G ≤ 5 ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  let C := P.elementaryChart hprimitive
  let x : X := Classical.arbitrary X
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hpow : P.p^C.d = 16 := by
    have he := P.degree_eq_prime_pow_finrank C.equiv x
    simpa only [PrimitiveAffineProfile.ElementaryChart.d,hdegree] using he.symm
  have hpdiv : P.p ∣ 2^4 := by
    change P.p ∣ 16
    rw [← hpow]
    exact dvd_pow_self _ C.d_pos.ne'
  have hp : P.p = 2 := Nat.prime_eq_prime_of_dvd_pow P.p_prime (by decide) hpdiv
  have hd : C.d = 4 := Nat.pow_right_injective (by decide : 2 ≤ 2)
    (by simpa only [hp] using hpow)
  let f0 : P.complement x →* Matrix.GeneralLinearGroup (Fin C.d) (ZMod P.p) :=
    FaithfulFiniteLinearRepresentationOrder.matrixHom
      (P.complementRepresentationCore hprimitive C x).ρ
  have hf0 : Function.Injective f0 :=
    FaithfulFiniteLinearRepresentationOrder.matrixHom_injective _
      (P.complementRepresentationCore_injective hprimitive C x)
  rcases complement_bound hclass P.p C.d hp hd f0 hf0 with hhead | hbad
  · exact Or.inl ((P.genRank_le_complement_add_one hprimitive x).trans (by omega))
  · exact Or.inr hbad

include P in
theorem genRank_le_sharpFloor_or_sporadic_counterexample
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hprimitive : MulAction.IsPreprimitive G X)
    (hdegree : Nat.card X = 16) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  rcases genRank_le_five_or_sporadic_counterexample P hclass hprimitive hdegree with hp | hbad
  · have hnum := _root_.SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction.five_le_sharpFloor_of_band
      16 (by decide) (by decide)
    exact Or.inl (hp.trans (by simpa only [hdegree] using hnum))
  · exact Or.inr hbad
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveAffineSixteenEightPointSharpReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveBoundedSharpTitsCompleteCFSGReduction
open _root_.SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpTitsCompleteCFSGReduction
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (J : Subgroup (Equiv.Perm (Fin n))) (hprimitive : MulAction.IsPreprimitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (PrimitiveAffineProfile J (Fin n))) ∨
      ∃ D : NonaffineData J (Fin n), ∃ s : CFSG.Sporadic,
        Nonempty (D.Simple ≃* (CFSG.Index.sporadic s).Model) := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  letI : MulAction.IsPreprimitive J (Fin n) := hprimitive
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveBoundedSharpCFSGReduction.genRank_le_sharpFloor_or_actual_residual
      hclass n hlo hhi J hprimitive with hpaid | haffine | ⟨D,j,hj,⟨e⟩⟩
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl haffine)
  · cases j <;> try exact hj.elim
    case tits =>
      have hpaid := PrimitiveSocleTitsBoundedSharp.genRank_le_sharpFloor D e
        (by simpa only [Nat.card_fin] using hhi)
      exact Or.inl (by simpa only [Nat.card_fin] using hpaid)
    case sporadic s => exact Or.inr (Or.inr ⟨D,s,⟨e⟩⟩)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveBoundedSharpTitsCompleteCFSGReduction

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpTitsCompleteActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpTitsCompleteActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  letI : MulAction.IsPretransitive J (Fin n) := ht
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  by_cases hp : MulAction.IsPreprimitive J (Fin n)
  · rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveBoundedSharpTitsCompleteCFSGReduction.genRank_le_sharpFloor_or_actual_residual
      hclass n hlo hhi J hp with hpaid | haffine | ⟨D,s,⟨e⟩⟩
    · exact Or.inl hpaid
    · obtain ⟨P⟩ := haffine.2
      rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveAffineSixteenEightPointSharpReduction.genRank_le_sharpFloor_or_sporadic_counterexample
          P hclass hp (by simpa only [Nat.card_fin] using haffine.1) with hpaid | hbad
      · exact Or.inl (by simpa only [Nat.card_fin] using hpaid)
      · obtain ⟨w⟩ := hbad
        let wprime := _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpPrimeProductSporadicReduction.refine_global
          (by decide : 8 ≤ 10) w
        let wcumulative := refine_global_cumulative (by decide : 8 ≤ 10) wprime
        exact Or.inr (Or.inl ⟨haffine.1,hp,⟨P⟩,⟨wcumulative⟩⟩)
    · have hs : n ≤ 10 → ¬GlobalExcluded s := by
        intro hn
        exact small_action_not_global_excluded D s e (by simpa only [Nat.card_fin] using hn)
      exact Or.inr (Or.inr (Or.inl ⟨hp,D,s,⟨e⟩,hs⟩))
  · let x₀ : Fin n := ⟨0,by omega⟩
    obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) x₀ hp
    letI : Fintype block.Points := Fintype.ofFinite _
    letI : Nontrivial block.Fibre := Finite.one_lt_card_iff_nontrivial.mp
      (by have hh := block.degrees_ge_two.1; omega)
    letI : MulAction.IsPreprimitive block.Component block.Fibre := block.component_preprimitive
    obtain ⟨P⟩ := publishedONanScottStructure block.Component block.Fibre
    cases P with
    | inr P =>
      rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalAffineBoundedSharpCoTwoTopRefinement.genRank_le_sharpFloor_or_cumulative_sporadic_obstructions
          J block P hclass (by omega) with hpaid | ⟨h16,htop⟩ | hglobal
      · exact Or.inl hpaid
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h16,ht,x₀,block,⟨P⟩,htop⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hglobal))))
    | inl D =>
      have hproduct : Nat.card block.Fibre * Nat.card block.Points = n := by
        simpa only [Nat.card_fin] using block.degree_product
      have hfibre : Nat.card block.Fibre ≤ 10 := by
        have htwo := block.degrees_ge_two.2
        nlinarith only [hproduct,htwo,hhi]
      rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.OriginalNonaffineBoundedSharpCFSGReduction.genRank_le_sharpFloor_or_actual_remaining_model
          J block D hclass (by omega) with hpaid | ⟨j,hj,⟨e⟩⟩
      · exact Or.inl hpaid
      · cases j <;> try exact hj.elim
        ·
          exact (PrimitiveSocleThirteenPointTitsExclusion.not_tits_of_degree_le_thirteen
            D (by omega) e).elim
        ·
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨ht,x₀,block,hfibre,D,_,⟨e⟩,?_⟩))))
          exact small_action_not_global_excluded D _ e hfibre
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpTitsCompleteActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpEightClosedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpEightClosedActualResidual
open TraceySharpHalfDegreeNumerics

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem not_primitive_affine_residual (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    ¬_root_.SymmetricSubgroupAsymptotics.BoundedSharpTitsCompleteActualResidual.PrimitiveAffineResidual J := by
  rintro ⟨h16,hp,hprofile,hbad⟩
  exact _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.EightPointHalfDegreeCompleteCFSG.no_cumulative_global_counterexample_eight hclass hbad

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4≤n) (hhi : n≤21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpTitsCompleteActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hbad
  · exact Or.inl hpaid
  · rcases hbad with haffine | hprimitive | htop | hglobal | hnonaffine
    · exact (not_primitive_affine_residual J hclass haffine).elim
    · exact Or.inr (Or.inl hprimitive)
    · exact (not_original_affine_top_residual J htop).elim
    · exact Or.inr (Or.inr (Or.inl hglobal))
    · exact Or.inr (Or.inr (Or.inr hnonaffine))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpEightClosedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpTenClosedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpTenClosedActualResidual
open TraceySharpHalfDegreeNumerics
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

 theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4≤n) (hhi : n≤21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpEightClosedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hbad
  · exact Or.inl hpaid
  · rcases hbad with hprimitive | hglobal | hnonaffine
    · exact Or.inr (Or.inl hprimitive)
    · exact (_root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.TenPointGlobalCounterexampleCompleteCFSG.no_cumulative_global_counterexample_ten
        hclass hglobal).elim
    · exact Or.inr (Or.inr hnonaffine)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpTenClosedActualResidual
