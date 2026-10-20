import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesHead
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesTrace
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding

/-! The actual imprimitive head compression, retaining every other original
point coordinate in its quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
open MarkedC4

/-- Construction output for the selected original head orbit.  All its
fields are proved from the original block chart and actual kernel trace. -/
structure HeadCompression (G X : Type) [Group G] [Fintype X]
    (S : ActionShape) where
  Q : Type
  Y : Type
  [groupQ : Group Q]
  [finiteQ : Finite Q]
  [solvableQ : IsSolvable Q]
  [fintypeY : Fintype Y]
  [nonemptyY : Nonempty Y]
  hom : Q →* (ActionShape.cons Y S).Coordinates
  injective : Function.Injective hom
  transitive : ActionShape.TransitiveProfile hom
  localDegree : ℕ
  local_ge_two : 2 ≤ localDegree
  top_ge_two : 2 ≤ Fintype.card Y
  degree_product : Fintype.card X = localDegree * Fintype.card Y
  top_lt : Fintype.card Y < Fintype.card X
  generators : (genRank G : ℝ) ≤ genRank Q +
    (traceyInducedGeneratorCeiling 1 (Fintype.card Y) : ℝ) *
      ((8 / 3 : ℝ) * Real.logb 2 localDegree - 4 / 3)

attribute [instance] HeadCompression.groupQ HeadCompression.finiteQ
  HeadCompression.solvableQ HeadCompression.fintypeY HeadCompression.nonemptyY

variable {G X : Type} [Group G] [Finite G] [IsSolvable G]
  [Fintype X] [Nonempty X] {S : ActionShape}

/-- Compress the primitive local component of an actual imprimitive head
orbit, with the whole ordinary source and all tail correlations retained. -/
theorem headCompression_nonempty
    (hTracey : TraceyRefinedInducedModuleInput)
    (hcomp : PrimitiveCompositionLengthInput)
    (f : G →* (ActionShape.cons X S).Coordinates)
    (hf : Function.Injective f)
    (hprofile : ActionShape.TransitiveProfile f)
    (hn : letI : MulAction G X := MulAction.compHom X (ActionShape.head f)
      ¬ MulAction.IsPreprimitive G X)
    (hr : 2 ≤ Fintype.card X) : Nonempty (HeadCompression G X S) := by
  letI : MulAction G X := MulAction.compHom X (ActionShape.head f)
  letI : MulAction.IsPretransitive G X := hprofile.1
  letI : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let h := ActionShape.head f
  let L := h.range
  let qL : G →* L := h.rangeRestrict
  letI : IsSolvable L := solvable_of_surjective
    (f := qL) h.rangeRestrict_surjective
  letI : MulAction.IsPretransitive L X := by
    constructor
    intro y z
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G y z
    exact ⟨qL g, hg⟩
  let eX : X →ₑ[qL] X := { toFun := id, map_smul' := by intros; rfl }
  have hnL : ¬ MulAction.IsPreprimitive L X := by
    intro hL
    apply hn
    exact (MulAction.isPreprimitive_congr h.rangeRestrict_surjective
      (show Function.Bijective eX from Function.bijective_id)).mpr hL
  let D := Classical.choice (originalMinimalBlock_nonempty (A := L) x hnL)
  let I := D.Points
  let T := D.Top
  let w0 := ActualBlockWreathEmbedding.embedding D.map D.map_equivariant D.base
  let w := w0.comp qL
  let rest := ActionShape.tail f
  letI : Nonempty I := ⟨D.base⟩
  letI : MulAction.IsPretransitive T I := D.top_pretransitive
  have htop : Function.Surjective (PermutationalWreathProduct.rightHom.comp w) := by
    intro t
    obtain ⟨l, hl⟩ := D.topMap.rangeRestrict_surjective t
    obtain ⟨g, hg⟩ := h.rangeRestrict_surjective l
    refine ⟨g, ?_⟩
    change D.topMap.rangeRestrict (qL g) = t
    rw [hg]
    exact hl
  have hjoint : ∀ g h : G, w g = w h → rest g = rest h → g = h := by
    intro g h hw hrest
    apply hf
    apply Prod.ext
    · have he : qL g = qL h :=
        ActualBlockWreathEmbedding.embedding_injective
          D.map D.map_equivariant D.base hw
      exact congrArg Subtype.val he
    · exact hrest
  let Q := SelectedTop.Top w rest
  let st := SelectedTop.state w rest htop hjoint
  let q : G →* Q := (SelectedTop.projection w rest).rangeRestrict
  letI : IsSolvable Q := solvable_of_surjective
    (f := q) (SelectedTop.projection w rest).rangeRestrict_surjective
  letI : IsSolvable D.Component := solvable_of_surjective
    (f := (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict)
    (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  let selected : Q →* Equiv.Perm I :=
    D.Top.subtype.comp (SelectedTop.selectedProjection w rest)
  let k : Q →* (ActionShape.cons I S).Coordinates :=
    selected.prod (SelectedTop.restProjection w rest)
  have hk : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hab
    · change SelectedTop.restProjection w rest a = SelectedTop.restProjection w rest b
      exact congrArg (fun z : (ActionShape.cons I S).Coordinates => z.2) hab
  have hkprofile : ActionShape.TransitiveProfile k := by
    refine ⟨?_, ?_⟩
    · have ht := SelectedTop.top_pretransitive w rest htop
      rcases ht with ⟨ht⟩
      constructor
      intro i j
      obtain ⟨a, ha⟩ := ht i j
      exact ⟨a, ha⟩
    · apply ActionShape.profile_of_comp (SelectedTop.restProjection w rest) q
      change ActionShape.TransitiveProfile rest
      exact hprofile.2
  have hs : 2 ≤ Fintype.card I := by
    simpa only [Nat.card_eq_fintype_card] using D.degrees_ge_two.2
  letI : IsSolvable st.D := by
    change IsSolvable D.Component
    infer_instance
  obtain ⟨c, hc⟩ := exists_chief_ordinary_generator_bound hTracey hs st
  obtain ⟨t, ht⟩ := actualChiefAbelianLength_le_some_compositionLength c
  have hlen := PrimitiveCompositionLengthInput.bound_of_equiv hcomp
    (Fintype.card D.Fibre)
    (by simpa only [Nat.card_eq_fintype_card] using D.degrees_ge_two.1)
    (Fintype.equivFin D.Fibre) D.Component D.component_preprimitive t
  have hcost : (genRank G : ℝ) ≤ genRank Q +
      (traceyInducedGeneratorCeiling 1 (Fintype.card I) : ℝ) *
        ((8 / 3 : ℝ) * Real.logb 2 (Fintype.card D.Fibre) - 4 / 3) := by
    have hcR : (genRank G : ℝ) ≤ genRank Q +
        (traceyInducedGeneratorCeiling 1 (Fintype.card I) : ℝ) *
          actualChiefSeriesAbelianLength c := by exact_mod_cast hc
    have htR : (actualChiefSeriesAbelianLength c : ℝ) ≤ t.chain.length := by
      exact_mod_cast ht
    have hmul := mul_le_mul_of_nonneg_left (htR.trans hlen)
      (show (0 : ℝ) ≤ (traceyInducedGeneratorCeiling 1 (Fintype.card I) : ℝ) from
        Nat.cast_nonneg _)
    linarith [hcR, hmul]
  refine ⟨{
    Q := Q
    Y := I
    groupQ := inferInstance
    finiteQ := inferInstance
    solvableQ := inferInstance
    fintypeY := inferInstance
    nonemptyY := inferInstance
    hom := k
    injective := hk
    transitive := hkprofile
    localDegree := Fintype.card D.Fibre
    local_ge_two := by simpa only [Nat.card_eq_fintype_card] using D.degrees_ge_two.1
    top_ge_two := hs
    degree_product := ?_
    top_lt := by simpa only [Nat.card_eq_fintype_card] using D.degrees_lt.2
    generators := hcost }⟩
  exact (show Fintype.card D.Fibre * Fintype.card I = Fintype.card X by
    simpa only [Nat.card_eq_fintype_card] using D.degree_product).symm

end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
