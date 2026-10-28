import SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharpOriginalBlocks
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
namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpTenClosedYExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpTenClosedYExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open PrimitiveSocleYSectionOrdinaryTail
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4≤n) (hhi : n≤21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpTenClosedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl (refine_primitive J hhi hp))
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpTenClosedYExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpMathieuAndJFourExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpTenClosedYExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · rcases refine_primitive J hhi hp with hpaid | hres
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpMathieuAndJFourExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpLargePrimePairsExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpLargePrimePairsExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleLargePrimePairBoundedSharp (LargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem refine_primitive (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : n ≤ 21)
    (h : _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual.PrimitiveSporadicResidual J) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew⟩ := h
  by_cases hs : LargePrimePairTag s
  · have hg := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_model
      D hclass (by simpa only [Nat.card_fin] using hhi) s hs e
    exact Or.inl (by simpa only [Nat.card_fin] using hg)
  · exact Or.inr ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hs⟩

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpMathieuAndJFourExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · rcases refine_primitive J hclass hhi hp with hpaid | hres
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpLargePrimePairsExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpMonsterExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMonsterExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleLargePrimePairBoundedSharp (LargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpLargePrimePairsExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl (refine_primitive J hhi hp))
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpMonsterExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleRuPrimeThirteenBoundedSharp
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleRuPrimeThirteenBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics

-- The checked Co3 installer uses this same opacity boundary: this file
-- transports group data, so array decoding must not enter group-instance
-- comparison. These remain the original literal definitions.
attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.Ru.rows1
  CFSG.Models.MatrixGroups.Ru.rows2

private theorem noncommutative_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hn : ¬IsMulCommutative A) : ¬IsMulCommutative B := by
  intro hc
  apply hn
  apply IsMulCommutative.of_comm
  intro a b
  apply e.injective
  rw [map_mul,map_mul]
  exact hc.is_comm.comm (e a) (e b)

private theorem pair_head_transport {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (hpair : CFSGGeneration.TwoGenerated B) : MarkedC4.genRank A ≤ 2 := by
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm hpair
  exact (MarkedC4.genRank_le hS).trans hcard

theorem genRank_le_sharpFloor_of_ru
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Ru.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  have hn : ¬IsMulCommutative CFSG.Models.MatrixGroups.Ru.Model :=
    @noncommutative_transport D.Simple CFSG.Models.MatrixGroups.Ru.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Ru.Model) e D.noncommutative
  have hd : 13 ∣ Nat.card D.Simple := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSGRuSelectedProductPrimeThirteen.thirteen_dvd_card hn
  have hhead : MarkedC4.genRank D.Simple ≤ 2 :=
    @pair_head_transport D.Simple CFSG.Models.MatrixGroups.Ru.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Ru.Model) e CFSGGeneration.ru_twoGenerated
  exact _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_prime
    D hclass hhi 13 (by decide) (by decide) hd hhead
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleRuPrimeThirteenBoundedSharp

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpRuPrimeThirteenExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpRuPrimeThirteenExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleRuPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem refine_primitive (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : n ≤ 21)
    (h : _root_.SymmetricSubgroupAsymptotics.BoundedSharpMonsterExcludedActualResidual.PrimitiveSporadicResidual J) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster⟩ := h
  by_cases hs : s=.ru
  · subst s
    have hg := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleRuPrimeThirteenBoundedSharp.genRank_le_sharpFloor_of_ru
      D hclass (by simpa only [Nat.card_fin] using hhi) e
    exact Or.inl (by simpa only [Nat.card_fin] using hg)
  · exact Or.inr ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,(fun hx => hx.elim hlarge hs),hmonster⟩

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpMonsterExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · rcases refine_primitive J hclass hhi hp with hpaid | hres
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpRuPrimeThirteenExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleSuzPrimeThirteenBoundedSharp
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSuzPrimeThirteenBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics

-- The checked Co3 installer uses this same opacity boundary: this file
-- transports group data, so array decoding must not enter group-instance
-- comparison. These remain the original literal definitions.
attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.Suz.rows1
  CFSG.Models.MatrixGroups.Suz.rows2

private theorem noncommutative_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hn : ¬IsMulCommutative A) : ¬IsMulCommutative B := by
  intro hc
  apply hn
  apply IsMulCommutative.of_comm
  intro a b
  apply e.injective
  rw [map_mul,map_mul]
  exact hc.is_comm.comm (e a) (e b)

private theorem pair_head_transport {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (hpair : CFSGGeneration.TwoGenerated B) : MarkedC4.genRank A ≤ 2 := by
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm hpair
  exact (MarkedC4.genRank_le hS).trans hcard

theorem genRank_le_sharpFloor_of_suz
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Suz.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  have hn : ¬IsMulCommutative CFSG.Models.MatrixGroups.Suz.Model :=
    @noncommutative_transport D.Simple CFSG.Models.MatrixGroups.Suz.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Suz.Model) e D.noncommutative
  have hd : 13 ∣ Nat.card D.Simple := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSGSuzSelectedProductPrimeThirteen.thirteen_dvd_card hn
  have hhead : MarkedC4.genRank D.Simple ≤ 2 :=
    @pair_head_transport D.Simple CFSG.Models.MatrixGroups.Suz.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Suz.Model) e CFSGGeneration.suz_twoGenerated
  exact _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_prime
    D hclass hhi 13 (by decide) (by decide) hd hhead
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleSuzPrimeThirteenBoundedSharp

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpSuzPrimeThirteenExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpSuzPrimeThirteenExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem refine_primitive (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : n ≤ 21)
    (h : _root_.SymmetricSubgroupAsymptotics.BoundedSharpRuPrimeThirteenExcludedActualResidual.PrimitiveSporadicResidual J) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster⟩ := h
  by_cases hs : s=.suz
  · subst s
    have hg := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleSuzPrimeThirteenBoundedSharp.genRank_le_sharpFloor_of_suz
      D hclass (by simpa only [Nat.card_fin] using hhi) e
    exact Or.inl (by simpa only [Nat.card_fin] using hg)
  · exact Or.inr ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,(fun hx => hx.elim hlarge hs),hmonster⟩

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpRuPrimeThirteenExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · rcases refine_primitive J hclass hhi hp with hpaid | hres
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpSuzPrimeThirteenExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpCoThreePrimeTwentyThreeExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpCoThreePrimeTwentyThreeExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpSuzPrimeThirteenExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl (refine_primitive J hhi hp))
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpCoThreePrimeTwentyThreeExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleJankoOnePrimeNineteenBoundedSharp
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleJankoOnePrimeNineteenBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics

 theorem genRank_le_sharpFloor_of_jankoOne
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.Presentations.J1.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm CFSGGeneration.j1_twoGenerated
  exact _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_prime
    D hclass hhi 19 (by decide) (by decide) (simple_nineteen_dvd D e)
      ((MarkedC4.genRank_le hS).trans hcard)
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleJankoOnePrimeNineteenBoundedSharp

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpJankoOnePrimeNineteenExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpJankoOnePrimeNineteenExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem refine_primitive (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : n ≤ 21)
    (h : _root_.SymmetricSubgroupAsymptotics.BoundedSharpCoThreePrimeTwentyThreeExcludedActualResidual.PrimitiveSporadicResidual J) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3⟩ := h
  by_cases hs : s=.j1
  · subst s
    have hg := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleJankoOnePrimeNineteenBoundedSharp.genRank_le_sharpFloor_of_jankoOne
      D hclass (by simpa only [Nat.card_fin] using hhi) e
    exact Or.inl (by simpa only [Nat.card_fin] using hg)
  · exact Or.inr ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hs⟩

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpCoThreePrimeTwentyThreeExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · rcases refine_primitive J hclass hhi hp with hpaid | hres
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpJankoOnePrimeNineteenExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleHNPrimeElevenBoundedSharp
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleHNPrimeElevenBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics

attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.HN.rows1
  CFSG.Models.MatrixGroups.HN.rows2

private theorem pair_head_transport {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (hpair : CFSGGeneration.TwoGenerated B) : MarkedC4.genRank A ≤ 2 := by
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm hpair
  exact (MarkedC4.genRank_le hS).trans hcard

set_option maxRecDepth 4096 in
theorem genRank_le_sharpFloor_of_hn
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.HN.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  have hhead : MarkedC4.genRank D.Simple ≤ 2 :=
    @pair_head_transport D.Simple CFSG.Models.MatrixGroups.HN.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.HN.Model) e CFSGGeneration.hn_twoGenerated
  exact _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_prime
    D hclass hhi 11 (by decide) (by decide) (simple_eleven_dvd D e) hhead
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleHNPrimeElevenBoundedSharp

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpHNPrimeElevenExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpHNPrimeElevenExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem refine_primitive (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : n ≤ 21)
    (h : _root_.SymmetricSubgroupAsymptotics.BoundedSharpJankoOnePrimeNineteenExcludedActualResidual.PrimitiveSporadicResidual J) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1⟩ := h
  by_cases hs : s=.hn
  · subst s
    have hg := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleHNPrimeElevenBoundedSharp.genRank_le_sharpFloor_of_hn
      D hclass (by simpa only [Nat.card_fin] using hhi) e
    exact Or.inl (by simpa only [Nat.card_fin] using hg)
  · exact Or.inr ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hs⟩

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpJankoOnePrimeNineteenExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · rcases refine_primitive J hclass hhi hp with hpaid | hres
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpHNPrimeElevenExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleThPrimeNineteenBoundedSharp
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleThPrimeNineteenBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics

attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.Th.rows1
  CFSG.Models.MatrixGroups.Th.rows2

private theorem pair_head_transport {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (hpair : CFSGGeneration.TwoGenerated B) : MarkedC4.genRank A ≤ 2 := by
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm hpair
  exact (MarkedC4.genRank_le hS).trans hcard

set_option maxRecDepth 4096 in
theorem genRank_le_sharpFloor_of_th
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.Th.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  have hhead : MarkedC4.genRank D.Simple ≤ 2 :=
    @pair_head_transport D.Simple CFSG.Models.MatrixGroups.Th.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.Th.Model) e CFSGGeneration.th_twoGenerated
  exact _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_prime
    D hclass hhi 19 (by decide) (by decide) (simple_nineteen_dvd D e) hhead
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleThPrimeNineteenBoundedSharp

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpThPrimeNineteenExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpThPrimeNineteenExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem refine_primitive (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : n ≤ 21)
    (h : _root_.SymmetricSubgroupAsymptotics.BoundedSharpHNPrimeElevenExcludedActualResidual.PrimitiveSporadicResidual J) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn⟩ := h
  by_cases hs : s=.th
  · subst s
    have hg := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleThPrimeNineteenBoundedSharp.genRank_le_sharpFloor_of_th
      D hclass (by simpa only [Nat.card_fin] using hhi) e
    exact Or.inl (by simpa only [Nat.card_fin] using hg)
  · exact Or.inr ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hs⟩

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpHNPrimeElevenExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · rcases refine_primitive J hclass hhi hp with hpaid | hres
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpThPrimeNineteenExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleONPrimeElevenBoundedSharp
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleONPrimeElevenBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics

attribute [local irreducible] CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators CFSG.Models.MatrixGroups.ON.rows1
  CFSG.Models.MatrixGroups.ON.rows2

private theorem pair_head_transport {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (hpair : CFSGGeneration.TwoGenerated B) : MarkedC4.genRank A ≤ 2 := by
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm hpair
  exact (MarkedC4.genRank_le hS).trans hcard

set_option maxRecDepth 4096 in
theorem genRank_le_sharpFloor_of_onan
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.MatrixGroups.ON.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  have hhead : MarkedC4.genRank D.Simple ≤ 2 :=
    @pair_head_transport D.Simple CFSG.Models.MatrixGroups.ON.Model D.group
      (inferInstance : Group CFSG.Models.MatrixGroups.ON.Model) e CFSGGeneration.onan_twoGenerated
  exact _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_prime
    D hclass hhi 11 (by decide) (by decide) (simple_eleven_dvd D e) hhead
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleONPrimeElevenBoundedSharp

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpLyONExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpLyONExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem refine_primitive (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : n ≤ 21)
    (h : _root_.SymmetricSubgroupAsymptotics.BoundedSharpThPrimeNineteenExcludedActualResidual.PrimitiveSporadicResidual J) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth⟩ := h
  by_cases hl : s=.ly
  · subst s
    exact (PrimitiveSocleLyPrimeSixtySevenExclusion.not_ly_of_degree_le_twentyOne
      D (by simpa only [Nat.card_fin] using hhi) e).elim
  by_cases ho : s=.onan
  · subst s
    have hg := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleONPrimeElevenBoundedSharp.genRank_le_sharpFloor_of_onan
      D hclass (by simpa only [Nat.card_fin] using hhi) e
    exact Or.inl (by simpa only [Nat.card_fin] using hg)
  · exact Or.inr ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hl,ho⟩

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpThPrimeNineteenExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · rcases refine_primitive J hclass hhi hp with hpaid | hres
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpLyONExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpCoOnePrimeElevenExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpCoOnePrimeElevenExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem refine_primitive (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hhi : n ≤ 21)
    (h : _root_.SymmetricSubgroupAsymptotics.BoundedSharpLyONExcludedActualResidual.PrimitiveSporadicResidual J) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ PrimitiveSporadicResidual J := by
  obtain ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hly,hon⟩ := h
  by_cases hs : s=.co1
  · subst s
    have hg := _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.PrimitiveSocleCoOnePrimeElevenBoundedSharp.genRank_le_sharpFloor_of_coOne
      D hclass (by simpa only [Nat.card_fin] using hhi) e
    exact Or.inl (by simpa only [Nat.card_fin] using hg)
  · exact Or.inr ⟨hp,D,s,⟨e⟩,hglobal,hY,hnew,hlarge,hmonster,hco3,hj1,hhn,hth,hly,hon,hs⟩

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpLyONExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · rcases refine_primitive J hclass hhi hp with hpaid | hres
    · exact Or.inl hpaid
    · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpCoOnePrimeElevenExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpCoTwoPrimeTwentyThreeExcludedActualResidual
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpCoTwoPrimeTwentyThreeExcludedActualResidual
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem genRank_le_sharpFloor_or_actual_residual
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ ActualResidual J := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpCoOnePrimeElevenExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hp | hb
  · exact Or.inl hpaid
  · exact Or.inr (Or.inl (refine_primitive J hhi hp))
  · exact Or.inr (Or.inr (refine_original_nonaffine J hb))
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpCoTwoPrimeTwentyThreeExcludedActualResidual

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpJankoTwoHeisenbergSingerCompleteCFSG
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpJankoTwoHeisenbergSingerCompleteCFSG
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleYSectionOrdinaryTail _root_.SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual (NewlyExcluded)
open _root_.SymmetricSubgroupAsymptotics.PrimitiveSocleSuzPrimeThirteenBoundedSharp (ExpandedLargePrimePairTag)
open _root_.SymmetricSubgroupAsymptotics.BoundedSharpCoTwoPrimeTwentyThreeExcludedActualResidual
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))

theorem genRank_le_sharpFloor
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n := by
  rcases _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpCoTwoPrimeTwentyThreeExcludedActualResidual.genRank_le_sharpFloor_or_actual_residual
    J hclass hlo hhi ht with hpaid | hbad
  · exact hpaid
  · exact False.elim (not_actual_residual J hhi hbad)

theorem exists_generating_finset
    (hclass : CFSGCatalogueWithAxiomMonster.Classification) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (ht : MulAction.IsPretransitive J (Fin n)) :
    ∃ U : Finset J,Subgroup.closure (U : Set J)=⊤ ∧ U.card ≤ sharpFloor n := by
  obtain ⟨U,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨U,hgen,hcard.le.trans (genRank_le_sharpFloor J hclass hlo hhi ht)⟩
end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpJankoTwoHeisenbergSingerCompleteCFSG

namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp

theorem boundedSharp_proved (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    TraceyPublished2018BoundedSharpPermutationInput := by
  intro n hlo hhi J ht
  exact _root_.SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp.BoundedSharpJankoTwoHeisenbergSingerCompleteCFSG.exists_generating_finset
    J hclass hlo (by omega) ht

def inputBundle_of_coarse (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (hTracey : TraceyPermutationGeneratorInput) : TraceyPublished2018PermutationInputBundle where
  coarse := hTracey
  boundedSharp := boundedSharp_proved hclass

theorem mcIverNeumann_of_coarse (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (hTracey : TraceyPermutationGeneratorInput) : McIverNeumannPermutationGeneratorBound :=
  (inputBundle_of_coarse hclass hTracey).mcIverNeumann

end SymmetricSubgroupAsymptotics.ExtendedCatalogueBoundedSharp
