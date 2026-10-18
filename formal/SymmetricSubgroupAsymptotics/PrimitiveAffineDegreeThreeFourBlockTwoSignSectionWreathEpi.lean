import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionLinearImage

/-!
# The proper two-sign section maps onto the ternary wreath comparator

Schur--Zassenhaus splits each literal proper section into its retained
ternary plane and an actual binary complement.  The action-compatible
`D8` recognition now maps that complement onto the standard dihedral top.
Together with the retained-plane coordinates this gives an epimorphism
onto the canonical semidirect model of `S₃ ≀ C₂`, and hence onto the
literal degree-six comparator itself.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
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

private abbrev G (w : ℕ) (U : PreE7NonPairActionClass w) :=
  preE7NonPairAction w U

/-- A fixed literal Schur complement in the actual proper section. -/
noncomputable def degreeThreeFourBlockTwoSignSectionComplement
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (N : TwoSignProperAxis (E block P)) :
    Subgroup (G w U ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N) :=
  Classical.choose
    (degreeThreeFourBlockTwoSignSectionComplement_exists
      block P hr hs hcomponent hbinary N)

theorem degreeThreeFourBlockTwoSignSectionComplement_isComplement
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (N : TwoSignProperAxis (E block P)) :
    Subgroup.IsComplement'
      (degreeThreeFourBlockTwoSignSectionBase block P N).ker
      (degreeThreeFourBlockTwoSignSectionComplement
        block P hr hs hcomponent hbinary N) :=
  Classical.choose_spec
    (degreeThreeFourBlockTwoSignSectionComplement_exists
      block P hr hs hcomponent hbinary N)

/-- The chosen complement maps onto the standard dihedral top. -/
noncomputable def degreeThreeFourBlockTwoSignSectionComplementD8Map
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    degreeThreeFourBlockTwoSignSectionComplement
        block P hr hs hcomponent hbinary N →*
      DegreeSixS3Wreath.D8 :=
  (degreeThreeFourBlockTwoSignSectionD8Map
      block P hr hs hcomponent hbinary htwo N).comp
    (degreeThreeFourBlockTwoSignSectionComplementTopEquiv
      block P N
      (degreeThreeFourBlockTwoSignSectionComplement
        block P hr hs hcomponent hbinary N)
      (degreeThreeFourBlockTwoSignSectionComplement_isComplement
        block P hr hs hcomponent hbinary N)).toMonoidHom

theorem degreeThreeFourBlockTwoSignSectionComplementD8Map_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignSectionComplementD8Map
        block P hr hs hcomponent hbinary htwo N) :=
  (degreeThreeFourBlockTwoSignSectionD8Map_surjective
      block P hr hs hcomponent hbinary htwo N).comp
    (degreeThreeFourBlockTwoSignSectionComplementTopEquiv
      block P N
      (degreeThreeFourBlockTwoSignSectionComplement
        block P hr hs hcomponent hbinary N)
      (degreeThreeFourBlockTwoSignSectionComplement_isComplement
        block P hr hs hcomponent hbinary N)).surjective

/-- The actual section kernel, transported isomorphically to the standard
ternary plane. -/
noncomputable def degreeThreeFourBlockTwoSignSectionKernelTernaryEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    (degreeThreeFourBlockTwoSignSectionBase block P N).ker ≃*
      DegreeSixS3Wreath.TernaryKernel :=
  (degreeThreeFourBlockTwoSignSectionQuotientChart
      block P N).equiv.symm.trans
    (degreeThreeFourBlockTwoSignSectionTernaryEquiv
      block P hr hs hcomponent hbinary htwo N).toMultiplicative

/-- The two maps above respect the actual complement action on the
section kernel. -/
theorem degreeThreeFourBlockTwoSignSectionSemidirect_compatible
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    let K := (degreeThreeFourBlockTwoSignSectionBase block P N).ker
    let H := degreeThreeFourBlockTwoSignSectionComplement
      block P hr hs hcomponent hbinary N
    ∀ h : H,
      (degreeThreeFourBlockTwoSignSectionKernelTernaryEquiv
          block P hr hs hcomponent hbinary htwo N).toMonoidHom.comp
          (((K.normalizerMonoidHom).comp
            (Subgroup.inclusion (K.normalizer_eq_top ▸ le_top))) h).toMonoidHom =
        (DegreeSixS3Wreath.monomialAction
          (degreeThreeFourBlockTwoSignSectionComplementD8Map
            block P hr hs hcomponent hbinary htwo N h)).toMonoidHom.comp
          (degreeThreeFourBlockTwoSignSectionKernelTernaryEquiv
            block P hr hs hcomponent hbinary htwo N).toMonoidHom := by
  dsimp only
  let K := (degreeThreeFourBlockTwoSignSectionBase block P N).ker
  let H := degreeThreeFourBlockTwoSignSectionComplement
    block P hr hs hcomponent hbinary N
  let chart := degreeThreeFourBlockTwoSignSectionQuotientChart block P N
  let c := degreeThreeFourBlockTwoSignSectionTernaryEquiv
    block P hr hs hcomponent hbinary htwo N
  let topEquiv := degreeThreeFourBlockTwoSignSectionComplementTopEquiv
    block P N H
      (degreeThreeFourBlockTwoSignSectionComplement_isComplement
        block P hr hs hcomponent hbinary N)
  intro h
  apply MonoidHom.ext
  intro k
  obtain ⟨v, rfl⟩ := chart.equiv.surjective k
  apply Multiplicative.toAdd.injective
  let action := ((K.normalizerMonoidHom).comp
    (Subgroup.inclusion (K.normalizer_eq_top ▸ le_top))) h
  have hconj := chart.conjugate (h :
    G w U ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N) v
  have hkernel :
      chart.equiv.symm
          (action (chart.equiv (Multiplicative.ofAdd v))) =
        Multiplicative.ofAdd
          ((degreeThreeFourBlockTwoSignSectionRepresentation block P N).ρ
            (topEquiv h) v) := by
    apply chart.equiv.injective
    rw [chart.equiv.apply_symm_apply]
    apply Subtype.ext
    simpa only [action, Subgroup.coe_inclusion,
      degreeThreeFourBlockTwoSignSectionComplementTopEquiv_apply,
      topEquiv] using hconj.symm
  have haction := degreeThreeFourBlockTwoSignSectionTernaryEquiv_action
    block P hr hs hcomponent hbinary htwo N (topEquiv h) v
  change
    c ((chart.equiv.symm
      (action (chart.equiv (Multiplicative.ofAdd v)))).toAdd) = _
  rw [hkernel]
  simp only [degreeThreeFourBlockTwoSignSectionKernelTernaryEquiv,
    degreeThreeFourBlockTwoSignSectionComplementD8Map,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  rw [DegreeSixS3Wreath.monomialAction_toAdd]
  simpa [degreeThreeFourBlockTwoSignSectionKernelTernaryEquiv,
    degreeThreeFourBlockTwoSignSectionComplementD8Map,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    degreeThreeFourBlockTwoSignSectionComplementTopEquiv_apply,
    topEquiv, c, chart, K, H, action] using haction

/-- Semidirect-product epimorphism from the literal split section to the
canonical split model of `S₃ ≀ C₂`. -/
noncomputable def degreeThreeFourBlockTwoSignSectionSemidirectMap
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    let K := (degreeThreeFourBlockTwoSignSectionBase block P N).ker
    let H := degreeThreeFourBlockTwoSignSectionComplement
      block P hr hs hcomponent hbinary N
    K ⋊[(K.normalizerMonoidHom).comp
        (Subgroup.inclusion (K.normalizer_eq_top ▸ le_top))] H →*
      DegreeSixS3Wreath.SemidirectModel :=
  SemidirectProduct.map
    (degreeThreeFourBlockTwoSignSectionKernelTernaryEquiv
      block P hr hs hcomponent hbinary htwo N).toMonoidHom
    (degreeThreeFourBlockTwoSignSectionComplementD8Map
      block P hr hs hcomponent hbinary htwo N)
    (degreeThreeFourBlockTwoSignSectionSemidirect_compatible
      block P hr hs hcomponent hbinary htwo N)

theorem degreeThreeFourBlockTwoSignSectionSemidirectMap_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignSectionSemidirectMap
        block P hr hs hcomponent hbinary htwo N) := by
  rintro ⟨v, d⟩
  obtain ⟨k, rfl⟩ :=
    (degreeThreeFourBlockTwoSignSectionKernelTernaryEquiv
      block P hr hs hcomponent hbinary htwo N).surjective v
  obtain ⟨h, rfl⟩ :=
    degreeThreeFourBlockTwoSignSectionComplementD8Map_surjective
      block P hr hs hcomponent hbinary htwo N d
  exact ⟨⟨k, h⟩, rfl⟩

/-- The actual proper section maps onto the literal degree-six wreath
comparator. -/
noncomputable def degreeThreeFourBlockTwoSignSectionWreathMap
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    (G w U ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N) →*
      DegreeSixS3Wreath.G :=
  DegreeSixS3Wreath.semidirectEquiv.symm.toMonoidHom.comp
    ((degreeThreeFourBlockTwoSignSectionSemidirectMap
      block P hr hs hcomponent hbinary htwo N).comp
        (degreeThreeFourBlockTwoSignSectionSemidirectEquiv
          block P N
          (degreeThreeFourBlockTwoSignSectionComplement
            block P hr hs hcomponent hbinary N)
          (degreeThreeFourBlockTwoSignSectionComplement_isComplement
            block P hr hs hcomponent hbinary N)).symm.toMonoidHom)

theorem degreeThreeFourBlockTwoSignSectionWreathMap_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignSectionWreathMap
        block P hr hs hcomponent hbinary htwo N) :=
  DegreeSixS3Wreath.semidirectEquiv.symm.surjective.comp
    ((degreeThreeFourBlockTwoSignSectionSemidirectMap_surjective
      block P hr hs hcomponent hbinary htwo N).comp
        (degreeThreeFourBlockTwoSignSectionSemidirectEquiv
          block P N
          (degreeThreeFourBlockTwoSignSectionComplement
            block P hr hs hcomponent hbinary N)
          (degreeThreeFourBlockTwoSignSectionComplement_isComplement
            block P hr hs hcomponent hbinary N)).symm.surjective)

/-- The binary kernel left above the degree-six wreath quotient has order
at most four. -/
theorem degreeThreeFourBlockTwoSignSectionWreathMap_kernel_card_le_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Nat.card (degreeThreeFourBlockTwoSignSectionWreathMap
      block P hr hs hcomponent hbinary htwo N).ker ≤ 4 := by
  let R := G w U ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N
  let pi := degreeThreeFourBlockTwoSignSectionWreathMap
    block P hr hs hcomponent hbinary htwo N
  have hR : Nat.card R ≤ 288 :=
    degreeThreeFourBlockTwoSignSectionQuotient_card_le_two_eighty_eight
      block P hr hs hcomponent hbinary htwo N
  have hfactor := pi.ker.card_mul_index
  have hindex : pi.ker.index = 72 := by
    rw [Subgroup.index_ker,
      pi.range_eq_top_of_surjective
        (degreeThreeFourBlockTwoSignSectionWreathMap_surjective
          block P hr hs hcomponent hbinary htwo N),
      Nat.card_congr Subgroup.topEquiv.toEquiv,
      DegreeSixS3Wreath.card_G]
  rw [hindex] at hfactor
  change Nat.card pi.ker * 72 = Nat.card R at hfactor
  change Nat.card pi.ker ≤ 4
  omega

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
