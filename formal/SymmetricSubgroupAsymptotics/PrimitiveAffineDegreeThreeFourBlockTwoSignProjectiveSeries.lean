import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignCentralSeries

/-!
# The actual projective kernel in the four-block two-sign branch

The literal signed quotient maps onto its actual four-point top.  In the
two-sign branch the kernel of this map is exactly the two-character pair
kernel, hence has order four.  This file transports that statement through
the signed quotient chart and applies the small binary central-series
theorem.

The result is an actual central order-two subgroup of the signed quotient.
After dividing by it, the remaining projective kernel is central and has
order at most two.  Thus the only remaining recognition step for the
`D8`/`D8 × C2` comparison is identification of this literal quotient; no
normal-subgroup census is needed.
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

private abbrev PairChart
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :=
  degreeThreeFourBlockPairChart block P hr hs hcomponent

/-- The actual four-point top retained by the signed quotient. -/
abbrev DegreeThreeFourBlockTwoSignProjectiveImage
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :=
  (PairChart block P hr hs hcomponent).frame.top.range

/-- The signed quotient followed by its literal four-point top map. -/
def degreeThreeFourBlockTwoSign_projectiveMap
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    (preE7NonPairAction w U ⧸ E block P) →*
      DegreeThreeFourBlockTwoSignProjectiveImage
        block P hr hs hcomponent :=
  (PairChart block P hr hs hcomponent).frame.top.rangeRestrict.comp
    (PairChart block P hr hs hcomponent).sourceEquiv.toMonoidHom

theorem degreeThreeFourBlockTwoSign_projectiveMap_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    Function.Surjective
      (degreeThreeFourBlockTwoSign_projectiveMap
        block P hr hs hcomponent) :=
  (PairChart block P hr hs hcomponent).frame.top.rangeRestrict_surjective.comp
    (PairChart block P hr hs hcomponent).sourceEquiv.surjective

/-- The projective kernel is literally the pair kernel, transported through
the signed quotient equivalence. -/
def degreeThreeFourBlockTwoSign_projectiveKernelEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    (degreeThreeFourBlockTwoSign_projectiveMap
        block P hr hs hcomponent).ker ≃*
      (PairChart block P hr hs hcomponent).frame.top.ker where
  toFun z := ⟨(PairChart block P hr hs hcomponent).sourceEquiv z.1,
    congrArg Subtype.val z.2⟩
  invFun k := ⟨(PairChart block P hr hs hcomponent).sourceEquiv.symm k.1, by
    apply Subtype.ext
    simpa only [degreeThreeFourBlockTwoSign_projectiveMap,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using k.2⟩
  left_inv z := by
    apply Subtype.ext
    exact (PairChart block P hr hs hcomponent).sourceEquiv.symm_apply_apply z.1
  right_inv k := by
    apply Subtype.ext
    exact (PairChart block P hr hs hcomponent).sourceEquiv.apply_symm_apply k.1
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (PairChart block P hr hs hcomponent).sourceEquiv a.1 b.1

/-- The actual projective kernel has order four. -/
theorem degreeThreeFourBlockTwoSign_projectiveKernel_card
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    Nat.card (degreeThreeFourBlockTwoSign_projectiveMap
      block P hr hs hcomponent).ker = 4 := by
  calc
    Nat.card (degreeThreeFourBlockTwoSign_projectiveMap
        block P hr hs hcomponent).ker =
        Nat.card (PairChart block P hr hs hcomponent).frame.top.ker :=
      Nat.card_congr
        (degreeThreeFourBlockTwoSign_projectiveKernelEquiv
          block P hr hs hcomponent).toEquiv
    _ = 4 := degreeThreeFourBlockTwoSign_pairKernel_card
      block P hr hs hcomponent htwo

/-- The signed quotient is a finite two-group in the binary branch. -/
theorem degreeThreeFourBlockTwoSign_signedQuotient_isPGroup
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action) :
    IsPGroup 2 (preE7NonPairAction w U ⧸ E block P) :=
  hbinary.of_equiv
    (PairChart block P hr hs hcomponent).sourceEquiv.symm

/-- The actual order-four projective kernel has a central series with two
binary factors.  The first factor is central in the signed quotient; the
second is central after quotienting the first. -/
noncomputable def degreeThreeFourBlockTwoSign_projectiveKernelCentralSeries
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    BinaryNormalKernelCentralSeries
      (preE7NonPairAction w U ⧸ E block P)
      (degreeThreeFourBlockTwoSign_projectiveMap
        block P hr hs hcomponent).ker := by
  let K := (degreeThreeFourBlockTwoSign_projectiveMap
    block P hr hs hcomponent).ker
  have hKcard : Nat.card K = 4 :=
    degreeThreeFourBlockTwoSign_projectiveKernel_card
      block P hr hs hcomponent htwo
  have hKne : K ≠ ⊥ := by
    intro h
    have hbot : Nat.card K = 1 := by rw [h, Subgroup.card_bot]
    omega
  exact binaryNormalKernelCentralSeries_of_card_le_four
    (degreeThreeFourBlockTwoSign_signedQuotient_isPGroup
      block P hr hs hcomponent hbinary)
    K hKne (by omega)

/-- The central order-two subgroup produced by the literal projective
kernel. -/
abbrev DegreeThreeFourBlockTwoSignCentralAxis
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    Subgroup (preE7NonPairAction w U ⧸ E block P) :=
  (degreeThreeFourBlockTwoSign_projectiveKernelCentralSeries
    block P hr hs hcomponent hbinary htwo).C

/-- The literal projective map descends after quotienting its central
order-two axis. -/
def degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    let C := DegreeThreeFourBlockTwoSignCentralAxis
      block P hr hs hcomponent hbinary htwo
    (preE7NonPairAction w U ⧸ E block P) ⧸ C →*
      DegreeThreeFourBlockTwoSignProjectiveImage
        block P hr hs hcomponent := by
  let pi := degreeThreeFourBlockTwoSign_projectiveMap
    block P hr hs hcomponent
  let S := degreeThreeFourBlockTwoSign_projectiveKernelCentralSeries
    block P hr hs hcomponent hbinary htwo
  exact QuotientGroup.lift S.C pi S.C_le_K

theorem degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    Function.Surjective
      (degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis
        block P hr hs hcomponent hbinary htwo) := by
  intro t
  obtain ⟨r, rfl⟩ :=
    degreeThreeFourBlockTwoSign_projectiveMap_surjective
      block P hr hs hcomponent t
  exact ⟨QuotientGroup.mk' _ r, rfl⟩

/-- The remaining kernel after the central quotient is central. -/
theorem degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis_central_kernel
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    ∀ z ∈ (degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis
        block P hr hs hcomponent hbinary htwo).ker,
      ∀ x, z * x = x * z := by
  let pi := degreeThreeFourBlockTwoSign_projectiveMap
    block P hr hs hcomponent
  let S := degreeThreeFourBlockTwoSign_projectiveKernelCentralSeries
    block P hr hs hcomponent hbinary htwo
  intro z hz x
  have hz' : z ∈ pi.ker.map (QuotientGroup.mk' S.C) := by
    simpa only [degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis,
      pi, S, QuotientGroup.ker_lift] using hz
  exact (Subgroup.mem_center_iff.mp (S.quotientKernel_le_center hz') x).symm

/-- The remaining central projective kernel has order at most two. -/
theorem degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis_kernel_card_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    Nat.card (degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis
      block P hr hs hcomponent hbinary htwo).ker ≤ 2 := by
  let pi := degreeThreeFourBlockTwoSign_projectiveMap
    block P hr hs hcomponent
  let K := pi.ker
  let S := degreeThreeFourBlockTwoSign_projectiveKernelCentralSeries
    block P hr hs hcomponent hbinary htwo
  let q : (preE7NonPairAction w U ⧸ E block P) →*
      (preE7NonPairAction w U ⧸ E block P) ⧸ S.C :=
    QuotientGroup.mk' S.C
  let L : Subgroup ((preE7NonPairAction w U ⧸ E block P) ⧸ S.C) :=
    K.map q
  let f : K →* L := q.subgroupMap K
  have hf : Function.Surjective f := q.subgroupMap_surjective K
  have hker : f.ker = S.C.subgroupOf K := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  have hkerCard : Nat.card f.ker = 2 := by
    rw [hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.C_le_K).toEquiv,
      S.C_card]
  have hKcard : Nat.card K = 4 :=
    degreeThreeFourBlockTwoSign_projectiveKernel_card
      block P hr hs hcomponent htwo
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hkerCard, hKcard] at hcard
  have hLcard : Nat.card L ≤ 2 := by omega
  have hkerLift :
      (degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis
        block P hr hs hcomponent hbinary htwo).ker = L := by
    simpa only [degreeThreeFourBlockTwoSign_projectiveMapAfterCentralAxis,
      pi, K, S, q, L, QuotientGroup.ker_lift]
  rw [hkerLift]
  exact hLcard

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
