import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionIsotypeCodimension
import SymmetricSubgroupAsymptotics.OriginalKernelLabelRegularEmbedding

/-!
# Literal pair-kernel action on a proper two-sign section

The pair kernel of the signed four-block quotient acts diagonally on the
original translation module.  This file descends that same literal action to
every proper rank-two section and records its displacement in the exact
normal-space intersection.  The statement is kept in the reindexed module
coordinates used by the two-sign isotype decomposition.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open DiagonalInvariantSubmodules
open DiagonalIsotypeProjection

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev G := preE7NonPairAction w U

local instance : Fact P.p.Prime := (chart block P).primeFact

/-- The literal pair kernel maps to the actual acting top of every proper
section.  This is the original quotient map `G/E → G/(E ⊔ N)`, restricted
through the fixed signed pair chart. -/
def degreeThreeFourBlockTwoSignSectionPairKernelTopHom
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (N : TwoSignProperAxis (E block P)) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    C.frame.top.ker →*
      G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
        degreeThreeFourBlockTwoSignSectionAxis block P N) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let pi := QuotientGroup.mk' (E block P)
  let M := degreeThreeFourBlockTwoSignSectionAxis block P N
  exact ((elementaryChart block P).originalKernelChart.labelTop
    pi M (QuotientGroup.mk'_surjective (E block P))).comp
      (C.sourceEquiv.symm.toMonoidHom.comp C.frame.top.ker.subtype)

@[simp] theorem degreeThreeFourBlockTwoSignSectionPairKernelTopHom_apply
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (N : TwoSignProperAxis (E block P))
    (k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker) :
    degreeThreeFourBlockTwoSignSectionPairKernelTopHom
        block P hr hs hcomponent N k =
      (elementaryChart block P).originalKernelChart.labelTop
        (QuotientGroup.mk' (E block P))
        (degreeThreeFourBlockTwoSignSectionAxis block P N)
        (QuotientGroup.mk'_surjective (E block P))
        ((degreeThreeFourBlockPairChart
          block P hr hs hcomponent).sourceEquiv.symm k.1) := rfl

/-- The pair-kernel representation on the retained rank-two section. -/
def degreeThreeFourBlockTwoSignSectionPairKernelRepresentation
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (N : TwoSignProperAxis (E block P)) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    Representation (ZMod P.p) C.frame.top.ker
      (DegreeThreeFourBlockTwoSignSectionModule block P N) :=
  (degreeThreeFourBlockTwoSignSectionRepresentation block P N).ρ.comp
    (degreeThreeFourBlockTwoSignSectionPairKernelTopHom
      block P hr hs hcomponent N)

/-- If one literal pair-kernel element acts trivially on the retained
section, its diagonal displacement on every ambient translation vector lies
in the reindexed normal-space intersection. -/
theorem degreeThreeFourBlockTwoSignSectionPairKernel_displacement_mem
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (N : TwoSignProperAxis (E block P))
    (k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker)
    (hk : degreeThreeFourBlockTwoSignSectionPairKernelRepresentation
      block P hr hs hcomponent N k = 1)
    (x : degreeThreeFourBlockReindexedTranslationSubmodule block P hs) :
    diagonalModuleOperator
          (degreeThreeFourBlockTranslationScalar
            block P hr hs hcomponent) k x.1 - x.1 ∈
      degreeThreeFourBlockReindexedSubrepresentation block P hs
        (degreeThreeFourBlockTwoSignSectionNormalSubrepresentation
          block P N) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let pi := QuotientGroup.mk' (E block P)
  let M := degreeThreeFourBlockTwoSignSectionAxis block P N
  let chart := (elementaryChart block P).originalKernelChart
  let I := degreeThreeFourBlockTwoSignSectionNormalSpace block P N
  let q : G ⧸ E block P := C.sourceEquiv.symm k.1
  let v : TranslationSubmodule block P :=
    (degreeThreeFourBlockReindexedTranslationEquiv block P hs).symm x
  have haction :
      (degreeThreeFourBlockTwoSignSectionRepresentation block P N).ρ
          (chart.labelTop pi M
            (QuotientGroup.mk'_surjective (E block P)) q)
          (I.mkQ v) = I.mkQ v := by
    have happ := congrArg
      (fun f : Module.End (ZMod P.p)
          (DegreeThreeFourBlockTwoSignSectionModule block P N) =>
        f (I.mkQ v)) hk
    simpa only [degreeThreeFourBlockTwoSignSectionPairKernelRepresentation,
      MonoidHom.comp_apply,
      degreeThreeFourBlockTwoSignSectionPairKernelTopHom_apply,
      Module.End.one_apply, C, pi, M, chart, I, q, v] using happ
  have hquot : I.mkQ
      ((elementaryChart block P).quotientRepresentation.ρ q v) = I.mkQ v := by
    rw [chart.sectionRepresentation_mkQ_top pi
      (elementaryChart block P).quotientRepresentation M
      (QuotientGroup.mk'_surjective (E block P)) q v]
    exact haction
  have hnormal :
      (elementaryChart block P).quotientRepresentation.ρ q v - v ∈ I :=
    (Submodule.Quotient.eq I).mp hquot
  refine ⟨
    (elementaryChart block P).quotientRepresentation.ρ q v - v,
    ?_, ?_⟩
  · simpa only [degreeThreeFourBlockTwoSignSectionNormalSubrepresentation,
      OriginalKernelModuleChart.normalSubrepresentation,
      degreeThreeFourBlockTwoSignSectionNormalSpace, pi, M, chart, I]
      using hnormal
  · rw [map_sub]
    have hdiag :=
      (degreeThreeFourBlockSignedTranslationCompatibility
        block P hr hs hcomponent).diagonal_action k v
    have hv : coordinateLinearEquiv (k := ZMod P.p)
        (degreeThreeFourBlockIndexEquiv block hs) v.1 = x.1 := by
      exact congrArg Subtype.val
        ((degreeThreeFourBlockReindexedTranslationEquiv
          block P hs).apply_symm_apply x)
    simpa only [C, q, v, hv] using congrArg
      (fun y => y - x.1) hdiag

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
