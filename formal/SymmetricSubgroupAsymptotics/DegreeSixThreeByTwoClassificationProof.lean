import SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoQuarterRecognition
import SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoModelRecognition
import SymmetricSubgroupAsymptotics.TwoTripleProductFrameRecognition
import SymmetricSubgroupAsymptotics.TransitiveTwoTripleSubgroupRecognition
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockProductFrame

/-! The actual two-triple wreath coordinates prove the former four-row
classification input. Nontrivial block-kernel signs supply four-divisibility;
the structural upper-image alternatives supply the literal model charts. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoClassificationProof
open Non2UnipotentPrefixFiniteMenu SemidirectProduct

theorem four_dvd_of_nontrivial_signs
    {U : PreE7NonPairActionClass 6} {basePoint : Fin 6}
    (D : OriginalMinimalBlock (A := preE7NonPairAction 6 U) basePoint)
    (hPoints : Nat.card D.Points = 2)
    (hSigns : DegreeThreeBlockInversionHead.coordinateSigns D.map D.map_equivariant ≠ 1) :
    4 ∣ Nat.card (preE7NonPairAction 6 U) := by
  have hex : ∃ x : D.Points, OriginalBlockSignCoordinates.coordinateSign
      D.map D.map_equivariant x ≠ 1 := by
    by_contra hn
    push Not at hn
    apply hSigns
    ext k x
    exact congrArg (fun f => f k) (hn x)
  obtain ⟨x,hx⟩ := hex
  let f := OriginalBlockSignCoordinates.coordinateSign D.map D.map_equivariant x
  have hn : f.range ≠ ⊥ := by
    intro h
    exact hx (MonoidHom.range_eq_bot_iff.mp h)
  have hgt : 1 < Nat.card f.range := f.range.one_lt_card_iff_ne_bot.mpr hn
  have hd : Nat.card f.range ∣ 2 := by
    have h := f.range.card_subgroup_dvd_card
    rwa [DegreeSixThreeByTwoProductRecognition.card_c2] at h
  have hc : Nat.card f.range = 2 := by
    have := Nat.le_of_dvd (by decide : 0<2) hd
    omega
  have heven : 2 ∣ Nat.card D.topMap.ker := by
    have h := Subgroup.card_range_dvd f
    rwa [hc] at h
  have hi : D.topMap.ker.index = 2 := by
    rw [Subgroup.index_ker]
    exact D.twoBlock_top_card hPoints
  have h := D.topMap.ker.card_mul_index
  obtain ⟨a,ha⟩ := heven
  refine ⟨a,?_⟩
  rw [hi,ha] at h
  omega

/-- The published three-by-two finite classification is a theorem of the
actual two-triple structural recognition, with no literature premise. -/
theorem publishedDegreeSixThreeByTwoAffineClassification :
    PublishedDegreeSixThreeByTwoAffineClassification := by
  intro U basePoint D _P hFibre hPoints hSigns
  let A := preE7NonPairAction 6 U
  letI : MulAction.IsPretransitive A (Fin 6) :=
    Non2TransitiveActionClass.representative_pretransitive U.1.1
  let F := D.productFrame (Finite.equivFinOfCardEq hPoints)
    ((Finite.equivFinOfCardEq hFibre).trans (ZMod.finEquiv 3).toEquiv)
  let c := TwoTripleProductFrameRecognition.conjugator F
  let P : Subgroup (Equiv.Perm (Fin 6)) := MulAut.conj c • A
  let E : A ≃* P := actionConjugacyEquiv c rfl
  let pointHom : MulActionHom E (Fin 6) (Fin 6) := {
    toFun := c
    map_smul' := by
      intro g x
      change c (g.1 x) = c (g.1 (c.symm (c x)))
      rw [c.symm_apply_apply] }
  letI : MulAction.IsPretransitive P (Fin 6) :=
    (MulAction.isPretransitive_congr (f := pointHom) E.surjective c.bijective).mp inferInstance
  have hle : P ≤ SixPairLocalWreathSocles.literalAction.range :=
    TwoTripleProductFrameRecognition.conjugate_le F
  have h4 : 4 ∣ Nat.card P :=
    Nat.card_congr E.toEquiv ▸ four_dvd_of_nontrivial_signs D hPoints hSigns
  have h6A : 6 ∣ Nat.card A := by
    have hi : (MulAction.stabilizer A (0 : Fin 6)).index = 6 := by
      simpa only [Nat.card_fin] using MulAction.index_stabilizer_of_transitive A (0 : Fin 6)
    simpa only [hi] using (MulAction.stabilizer A (0 : Fin 6)).index_dvd_card
  have h6 : 6 ∣ Nat.card P := Nat.card_congr E.toEquiv ▸ h6A
  let H := P.comap SixPairLocalWreathSocles.literalAction
  let Upper := TwoTripleFullUpperForcesFullWreath.Upper
  let upper := TwoTripleFullUpperForcesFullWreath.upper
  let V : Subgroup Upper := H.map upper
  let pi : H →* P := (SixPairLocalWreathSocles.literalAction.comp H.subtype).codRestrict P
    (fun g => g.2)
  have hpi : Function.Surjective pi := by
    intro p
    obtain ⟨g,hg⟩ := hle p.2
    exact ⟨⟨g,by change SixPairLocalWreathSocles.literalAction g ∈ P; rw [hg]; exact p.2⟩,
      Subtype.ext hg⟩
  obtain ⟨p,hp⟩ := MulAction.exists_smul_eq P (0 : Fin 6) 1
  obtain ⟨g,hg⟩ := hle p.2
  have hgH : g ∈ H := by
    change SixPairLocalWreathSocles.literalAction g ∈ P
    rw [hg]
    exact p.2
  have hgswap : g.right = C2Wreath.gen :=
    TwoTripleProperUpperModelCovers.swap_of_point g (by rw [hg]; exact hp)
  have hswap : ∃ u : Upper, u ∈ V ∧ u.right = C2Wreath.gen :=
    ⟨upper g,⟨g,hgH,rfl⟩,hgswap⟩
  rcases TwoTripleBinaryUpperRecognition.subgroup_cases V hswap with haxes | hquarter | hfull
  · have haxesP : P ≤ SixPointTernaryAxesNormalGenerators.literalAction.range := by
      intro p hp
      obtain ⟨k,hk⟩ := hle hp
      have hkH : k ∈ H := by
        change SixPairLocalWreathSocles.literalAction k ∈ P
        rwa [hk]
      have hu := haxes (show upper k ∈ V from ⟨k,hkH,rfl⟩)
      exact ⟨TwoTripleProperUpperModelCovers.axesWitness k,
        (TwoTripleProperUpperModelCovers.axes_cover k hu).trans hk⟩
    exact DegreeSixThreeByTwoModelRecognition.axes_source P E haxesP h4 h6
  · have hquarterP : P ≤ SixPointTernaryQuarterTurnNormalGenerators.literalAction.range := by
      intro p hp
      obtain ⟨k,hk⟩ := hle hp
      have hkH : k ∈ H := by
        change SixPairLocalWreathSocles.literalAction k ∈ P
        rwa [hk]
      have hu := hquarter (show upper k ∈ V from ⟨k,hkH,rfl⟩)
      exact ⟨TwoTripleProperUpperModelCovers.quarterWitness k,
        (TwoTripleProperUpperModelCovers.quarter_cover k hu).trans hk⟩
    let q := TwoTripleProperUpperModelCovers.quarterWitness g
    have hqmem : SixPointTernaryQuarterTurnNormalGenerators.literalAction q ∈ P := by
      rw [TwoTripleProperUpperModelCovers.quarter_cover g
        (hquarter (show upper g ∈ V from ⟨g,hgH,rfl⟩))]
      exact hgH
    rcases TwoTripleProperUpperModelCovers.quarter_swap g hgswap with hq | hq
    · exact ⟨.threeSquaredC4 (DegreeSixThreeByTwoQuarterRecognition.source P E
        hquarterP q hqmem hq)⟩
    · have hqinv : SixPointTernaryQuarterTurnNormalGenerators.literalAction q⁻¹ ∈ P := by
        simpa only [map_inv] using P.inv_mem hqmem
      change q.right = SixPointTernaryQuarterTurnNormalGenerators.gen⁻¹ at hq
      have hqinvR : (q⁻¹).right = SixPointTernaryQuarterTurnNormalGenerators.gen := by
        simp only [SemidirectProduct.inv_right,hq,inv_inv]
      exact ⟨.threeSquaredC4 (DegreeSixThreeByTwoQuarterRecognition.source P E
        hquarterP q⁻¹ hqinv hqinvR)⟩
  · have hU : ∀ u : Upper, ∃ k : TwoTripleFullUpperForcesFullWreath.Model,
        k ∈ H ∧ upper k = u := by
      intro u
      have hu : u ∈ V := by rw [hfull]; trivial
      exact hu
    have hH : H = ⊤ := TwoTripleFullUpperForcesFullWreath.eq_top_of_full_upper_nonzero_kernel
      H hU (TwoTripleFullUpperForcesFullWreath.kernel_nontrivial_of_transitive_image H P pi hpi)
    have hP : P = SixPairLocalWreathSocles.literalAction.range := by
      apply le_antisymm hle
      rintro _ ⟨k,rfl⟩
      have hk : k ∈ H := by rw [hH]; trivial
      exact hk
    exact ⟨DegreeSixThreeByTwoModelRecognition.full_source P E hP⟩

end SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoClassificationProof
