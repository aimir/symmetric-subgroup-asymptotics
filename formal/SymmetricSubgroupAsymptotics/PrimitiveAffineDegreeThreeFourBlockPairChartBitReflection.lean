import SymmetricSubgroupAsymptotics.BinaryPairFrameKernelTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockPairPackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePairFrameBitReflection

/-!
# Reflection of the four-block pair-chart bits

The fixed degree-eight chart is obtained from the literal signed quotient by
relabeling physical points and then the four original block indices.  The
generic pair-kernel transport identities therefore carry the pre-relabel
bit reflection to the exact chart used by the numerical degree-two package.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The element of the pre-relabel pair kernel belonging to an element of
the fixed four-pair-chart kernel. -/
noncomputable def degreeThreeFourBlockOriginalPairKernelElement
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker) :
    (degreeThreeSignedQuotientPairFrame block P hr).top.ker := by
  let e : Fin (quotientDegree block) ≃ Fin (2 * 4) := finCongr (by
    rw [quotientDegree_eq block, hr, hs])
  let F₀ := degreeThreeSignedQuotientPairFrame block P hr
  let F₁ := F₀.relabelPoints e
  let idx : block.Points ≃ Fin 4 := Finite.equivFinOfCardEq hs
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let q := C.sourceEquiv.symm k.1
  have hsource : C.sourceEquiv q = k.1 := C.sourceEquiv.apply_symm_apply k.1
  have hk : C.frame.top k.1 = 1 := k.2
  rw [← hsource] at hk
  refine ⟨degreeThreeSignedQuotientRangeEquiv block P q, ?_⟩
  apply Equiv.ext
  intro j
  have hj := congrArg
    (fun sigma : Equiv.Perm (Fin 4) => sigma (Finite.equivFinOfCardEq hs j)) hk
  have hchart :
      C.frame.top (C.sourceEquiv q) (Finite.equivFinOfCardEq hs j) =
        (Finite.equivFinOfCardEq hs)
          ((degreeThreeSignedQuotientPairFrame block P hr).top
            (degreeThreeSignedQuotientRangeEquiv block P q) j) := by
    change (F₁.reindex idx).top
      (BinaryPairFrame.sourceRelabelEquiv
        (U := (quotientAction block P).range) e
        (degreeThreeSignedQuotientRangeEquiv block P q)) (idx j) =
      idx (F₀.top (degreeThreeSignedQuotientRangeEquiv block P q) j)
    rw [F₁.reindex_top_apply, idx.symm_apply_apply,
      F₀.relabelPoints_top_sourceRelabelEquiv]
  change C.frame.top (C.sourceEquiv q) (Finite.equivFinOfCardEq hs j) =
    (1 : Equiv.Perm (Fin 4)) (Finite.equivFinOfCardEq hs j) at hj
  have hone : (1 : Equiv.Perm (Fin 4)) (Finite.equivFinOfCardEq hs j) =
      Finite.equivFinOfCardEq hs j := rfl
  rw [hchart, hone] at hj
  change (degreeThreeSignedQuotientPairFrame block P hr).top
    (degreeThreeSignedQuotientRangeEquiv block P q) j = j
  exact (Finite.equivFinOfCardEq hs).injective hj

@[simp] theorem degreeThreeFourBlockOriginalPairKernelElement_val
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker) :
    (degreeThreeFourBlockOriginalPairKernelElement
      block P hr hs hcomponent k).1 =
      degreeThreeSignedQuotientRangeEquiv block P
        ((degreeThreeFourBlockPairChart block P hr hs hcomponent).sourceEquiv.symm
          k.1) := by
  dsimp [degreeThreeFourBlockOriginalPairKernelElement]

/-- The bit retained by the fixed four-pair chart is the local-complement
bit in the corresponding original block. -/
theorem degreeThreeFourBlockPairChart_bits_eq_localBit
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker)
    (i : Fin 4) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    let q := C.sourceEquiv.symm k.1
    C.frame.bits k i =
      degreeThreeLocalBit block P hr
        ((quotientEmbedding block P q).left
          ((Finite.equivFinOfCardEq hs).symm i)) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let q := C.sourceEquiv.symm k.1
  let e : Fin (quotientDegree block) ≃ Fin (2 * 4) := finCongr (by
    rw [quotientDegree_eq block, hr, hs])
  let F₀ := degreeThreeSignedQuotientPairFrame block P hr
  let F₁ := F₀.relabelPoints e
  let idx : block.Points ≃ Fin 4 := Finite.equivFinOfCardEq hs
  let k₀ := degreeThreeFourBlockOriginalPairKernelElement
    block P hr hs hcomponent k
  let k' := F₁.reindexKernel idx (F₀.relabelKernel e k₀)
  have hk' : k' = k := by
    have hk₀ : k₀.1 = degreeThreeSignedQuotientRangeEquiv block P q := by
      simpa only [k₀, q, C] using
        degreeThreeFourBlockOriginalPairKernelElement_val
          block P hr hs hcomponent k
    apply Subtype.ext
    dsimp [k', BinaryPairFrame.reindexKernel,
      BinaryPairFrame.relabelKernel]
    change BinaryPairFrame.sourceRelabelEquiv
      (U := (quotientAction block P).range) e k₀.1 = k.1
    rw [hk₀]
    simpa only [C, q, degreeThreeFourBlockPairChart,
      degreeThreeSignedQuotientPairChart, MulEquiv.trans_apply] using
        C.sourceEquiv.apply_symm_apply k.1
  rw [← hk']
  change (F₁.reindex idx).bits k' i = _
  rw [BinaryPairFrame.reindexKernel_bits,
    BinaryPairFrame.relabelKernel_bits]
  exact degreeThreeSignedQuotientPairFrame_bits_eq_localBit
    block P hr k₀ (idx.symm i)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
