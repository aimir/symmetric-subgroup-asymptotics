import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallCatalogueCapacity
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge

/-! Isolated binary-small consumer route. Original datatypes, interfaces,
and finite certificate declarations are imported unchanged. Only the
changed consumer declarations and their private helper closure are copied. -/
set_option autoImplicit false

noncomputable section

open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu

namespace PrimitiveAffineImprimitiveBlockTransfer

namespace BinarySmallReduced

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}

theorem affineQuotientTrace_abelianLength_le_rowCap
    (D : BinaryAffineSmallCatalogueData)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    [Nontrivial block.Fibre]
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hnonsolvable : ¬ IsSolvable (P.complement (origin block)))
    (hdegree : Nat.card block.Fibre = 8 ∨ Nat.card block.Fibre = 16) :
    ∃ r : SmallAffineCatalogueRow,
      r.degree = Nat.card block.Fibre ∧
      r.nonsoluble = true ∧
      (affineQuotientTrace hTraceyHalf hTraceyLog hTraceyRefined
        hTraceyPerm block P).tower.abelianLength ≤
          r.nonsolubleAbelianCap := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let Q := affineQuotientTrace hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P
  let e := P.quotientComplementEquiv (origin block)
  let s : ActualChiefSeries (P.complement (origin block)) :=
    actualChiefSeriesComap e.symm Q.chief
  obtain ⟨r, hr, hn, hcap⟩ :=
    BinaryAffineSmallCatalogueBridge.chief_abelianLength_le_rowCap
      D block.component_preprimitive P
        (origin block) s hnonsolvable hdegree
  refine ⟨r, hr, hn, ?_⟩
  calc
    Q.tower.abelianLength = actualChiefSeriesAbelianLength Q.chief :=
      Q.abelianLength_eq
    _ = actualChiefSeriesAbelianLength s := by
      exact (actualChiefSeriesComap_abelianLength e.symm Q.chief).symm
    _ ≤ r.nonsolubleAbelianCap := hcap

private theorem degreeEight_translationDimension
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    [Nontrivial block.Fibre]
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 8) :
    (P.elementaryChart block.component_preprimitive).d = 3 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree : 8 = P.p ^ C.d := by
    rw [← hr]
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  exact (prime_pow_positive_injective (d := C.d) (e := 3)
    P.p_prime Nat.prime_two C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))).2

private theorem degreeSixteen_translationDimension
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    [Nontrivial block.Fibre]
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 16) :
    (P.elementaryChart block.component_preprimitive).d = 4 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree : 16 = P.p ^ C.d := by
    rw [← hr]
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  exact (prime_pow_positive_injective (d := C.d) (e := 4)
    P.p_prime Nat.prime_two C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))).2

theorem locate_soluble_component_order
    (D : BinaryAffineSmallCatalogueData)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hdegree : Nat.card block.Fibre = 8 ∨ Nat.card block.Fibre = 16)
    (hsolvable : IsSolvable (P.complement (origin block))) :
    ∃ r : SmallAffineCatalogueRow,
      r.degree = Nat.card block.Fibre ∧ r.nonsoluble = false ∧
      Nat.card block.Component =
        Nat.card block.Fibre * r.complementOrder := by
  obtain ⟨r, hr, hs, hcard⟩ :=
    BinaryAffineSmallCatalogueBridge.locate_soluble
      D block.component_preprimitive P
        (origin block) hdegree hsolvable
  refine ⟨r, hr, hs, ?_⟩
  have hfactor := (P.isComplement'_complement (origin block)).card_mul
  have hV : Nat.card P.V = Nat.card block.Fibre := P.card_eq (origin block)
  rw [← hfactor, hV, hcard]

theorem component_card_dvd_168_of_degreeEight_soluble
    (D : BinaryAffineSmallCatalogueData)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 8)
    (hsolvable : IsSolvable (P.complement (origin block))) :
    Nat.card block.Component ∣ 168 := by
  have hcomp :=
    BinaryAffineSmallCatalogueBridge.degreeEight_soluble_card_dvd_twentyOne
      D block.component_preprimitive P
        (origin block) hr hsolvable
  have hfactor := (P.isComplement'_complement (origin block)).card_mul
  have hV : Nat.card P.V = Nat.card block.Fibre := P.card_eq (origin block)
  rw [hfactor.symm, hV, hr]
  simpa using Nat.mul_dvd_mul_left 8 hcomp

theorem component_card_dvd_5760_of_degreeSixteen_soluble
    (D : BinaryAffineSmallCatalogueData)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : Nat.card block.Fibre = 16)
    (hsolvable : IsSolvable (P.complement (origin block))) :
    Nat.card block.Component ∣ 5760 := by
  have hcomp :=
    BinaryAffineSmallCatalogueBridge.degreeSixteen_soluble_card_dvd_threeSixty
      D block.component_preprimitive P
        (origin block) hr hsolvable
  have hfactor := (P.isComplement'_complement (origin block)).card_mul
  have hV : Nat.card P.V = Nat.card block.Fibre := P.card_eq (origin block)
  rw [hfactor.symm, hV, hr]
  simpa using Nat.mul_dvd_mul_left 16 hcomp

namespace ComponentSource

open _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource

variable
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

noncomputable def of_degreeEight_nonsoluble
    (D : BinaryAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 8)
    (hnonsolvable : ¬ IsSolvable (P.complement (origin block))) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
  refine ⟨?_⟩
  have hq := _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.affineQuotientTrace_abelianLength_le_rowCap D hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm block P hnonsolvable (Or.inl hr)
  obtain ⟨r, hrRow, hnRow, hcap⟩ := hq
  have hcap0 : r.nonsolubleAbelianCap ≤ 0 :=
    SmallAffineCatalogueRow.degreeEight_cap_le r (hrRow.trans hr) hnRow
  have hlen : T.abelianLength ≤ 3 := by
    rw [show T = (affineTrace hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P).tower from rfl,
      affineTrace_abelianLength_eq hTraceyHalf hTraceyLog hTraceyRefined
        hTraceyPerm block P,
      degreeEight_translationDimension block P hr]
    omega
  have hv : T.envelope.v = Nat.card block.Points := by
    simpa only [T, tower, Fintype.card_eq_nat_card] using
      ActualWreathCompressionTower.envelope_v T
  change preE7CharacterRho * (w : ℝ) ≤
    ((evenWidth w : ℝ) - (T.envelope.v : ℝ)) / 8 - T.envelope.eta
  rw [hv]
  apply smallAffine_budget_margin 8 (Nat.card block.Points) w
    block.degrees_ge_two.2 (by simpa only [hr] using width_eq block)
    ((3 / 2 : ℝ) * fixedTargetCompositionGamma) T.envelope.eta
  · have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
    unfold preE7CharacterRho
    norm_num at hgamma ⊢
    linarith
  · have heta := ActualWreathCompressionTower.envelope_eta_le_abelianLength T
    have hfactor : 0 ≤ fixedTargetCompositionGamma *
        ((Nat.card block.Points : ℝ) / 2) := by
      exact mul_nonneg
        (div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num))
        (by positivity)
    calc
      T.envelope.eta ≤ fixedTargetCompositionGamma *
          ((Nat.card block.Points : ℝ) / 2) * T.abelianLength := by
        simpa only [Fintype.card_eq_nat_card] using heta
      _ ≤ fixedTargetCompositionGamma *
          ((Nat.card block.Points : ℝ) / 2) * 3 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hlen) hfactor
      _ = ((3 / 2 : ℝ) * fixedTargetCompositionGamma) *
          Nat.card block.Points := by ring

noncomputable def of_degreeSixteen_nonsoluble
    (D : BinaryAffineSmallCatalogueData)
    (hr : Nat.card block.Fibre = 16)
    (hnonsolvable : ¬ IsSolvable (P.complement (origin block))) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
  refine ⟨?_⟩
  have hq := _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.affineQuotientTrace_abelianLength_le_rowCap D hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm block P hnonsolvable
      (Or.inr hr)
  obtain ⟨r, hrRow, hnRow, hcap⟩ := hq
  have hcap2 : r.nonsolubleAbelianCap ≤ 2 :=
    SmallAffineCatalogueRow.degreeSixteen_cap_le r (hrRow.trans hr) hnRow
  have hlen : T.abelianLength ≤ 6 := by
    rw [show T = (affineTrace hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P).tower from rfl,
      affineTrace_abelianLength_eq hTraceyHalf hTraceyLog hTraceyRefined
        hTraceyPerm block P,
      degreeSixteen_translationDimension block P hr]
    omega
  have hv : T.envelope.v = Nat.card block.Points := by
    simpa only [T, tower, Fintype.card_eq_nat_card] using
      ActualWreathCompressionTower.envelope_v T
  change preE7CharacterRho * (w : ℝ) ≤
    ((evenWidth w : ℝ) - (T.envelope.v : ℝ)) / 8 - T.envelope.eta
  rw [hv]
  apply smallAffine_budget_margin 16 (Nat.card block.Points) w
    block.degrees_ge_two.2 (by simpa only [hr] using width_eq block)
    (3 * fixedTargetCompositionGamma) T.envelope.eta
  · have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
    unfold preE7CharacterRho
    norm_num at hgamma ⊢
    linarith
  · have heta := ActualWreathCompressionTower.envelope_eta_le_abelianLength T
    have hfactor : 0 ≤ fixedTargetCompositionGamma *
        ((Nat.card block.Points : ℝ) / 2) := by
      exact mul_nonneg
        (div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num))
        (by positivity)
    calc
      T.envelope.eta ≤ fixedTargetCompositionGamma *
          ((Nat.card block.Points : ℝ) / 2) * T.abelianLength := by
        simpa only [Fintype.card_eq_nat_card] using heta
      _ ≤ fixedTargetCompositionGamma *
          ((Nat.card block.Points : ℝ) / 2) * 6 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hlen) hfactor
      _ = (3 * fixedTargetCompositionGamma) * Nat.card block.Points := by ring

end ComponentSource

end BinarySmallReduced

end PrimitiveAffineImprimitiveBlockTransfer

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end

