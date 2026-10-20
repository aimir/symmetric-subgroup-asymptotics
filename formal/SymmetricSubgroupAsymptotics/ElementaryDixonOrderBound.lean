import SymmetricSubgroupAsymptotics.ElementaryAffineDixonOrder
import SymmetricSubgroupAsymptotics.ActualThreeByTwoWreathCard
import SymmetricSubgroupAsymptotics.MarkedC4SolubleContainerOrder

/-! The ordinary soluble permutation order bound follows by faithful
minimal-block and orbit induction from the primitive order estimate. All
components, tops, and orbit images are the actual permutation images. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.ElementaryDixonOrderProof
open Non2UnipotentPrefixFiniteMenu

theorem transitive_order
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hstructure : PrimitiveSocleRawStructure.PublishedONanScottStructure)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] [Nonempty X]
    [IsSolvable G] : Nat.card G ^ 3 ≤ 24 ^ (Nat.card X - 1) := by
  suffices h : ∀ n : ℕ, ∀ (A Y : Type) [Group A] [Finite A] [Finite Y]
      [MulAction A Y] [FaithfulSMul A Y] [MulAction.IsPretransitive A Y]
      [Nonempty Y] [IsSolvable A], Nat.card Y = n →
      Nat.card A ^ 3 ≤ 24 ^ (n - 1) by
    exact h (Nat.card X) G X rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A Y _ _ _ _ _ _ _ _ hcard
    by_cases hY : Subsingleton Y
    · letI := hY
      letI : Subsingleton A := ⟨fun a b =>
        eq_of_smul_eq_smul (α := Y) (fun y => Subsingleton.elim _ _)⟩
      have ha : Nat.card A = 1 := Nat.card_eq_one_iff_unique.mpr
        ⟨inferInstance, inferInstance⟩
      rw [ha]
      simpa only [one_pow] using Nat.succ_le_of_lt
        (pow_pos (by decide : 0 < 24) (n - 1))
    · letI : Nontrivial Y := not_subsingleton_iff_nontrivial.mp hY
      by_cases hprimitive : MulAction.IsPreprimitive A Y
      · letI := hprimitive
        simpa only [hcard] using primitive_order catalogue hstructure A Y
      · let x : Y := Classical.arbitrary Y
        let D := Classical.choice (originalMinimalBlock_nonempty (A := A) x hprimitive)
        letI : IsSolvable D.Component := solvable_of_surjective
          (f := (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict)
          (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
        letI : IsSolvable D.Top := solvable_of_surjective
          (f := D.topMap.rangeRestrict) D.topMap.rangeRestrict_surjective
        letI : Nontrivial D.Fibre := Finite.one_lt_card_iff_nontrivial.mp
          (by have := D.degrees_ge_two.1; omega)
        letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
        letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
        letI : Nonempty D.Points := ⟨D.base⟩
        have hC := primitive_order catalogue hstructure D.Component D.Fibre
        have hT := ih (Nat.card D.Points) (by
          have := D.degrees_lt.2; omega) D.Top D.Points rfl
        let W := PermutationalWreathProduct D.Component D.Top D.Points
        letI : Finite W := Finite.of_equiv ((D.Points → D.Component) × D.Top)
          PermutationalWreathProduct.coordinateEquiv.symm
        have hG : Nat.card A ≤ Nat.card D.Component ^ Nat.card D.Points * Nat.card D.Top := by
          simpa only [PermutationalWreathProduct.natCard] using
            Nat.card_le_card_of_injective
              (ActualBlockWreathEmbedding.embedding D.map D.map_equivariant D.base)
              (ActualBlockWreathEmbedding.embedding_injective D.map D.map_equivariant D.base)
        calc
          Nat.card A ^ 3 ≤
              (Nat.card D.Component ^ Nat.card D.Points * Nat.card D.Top) ^ 3 :=
            Nat.pow_le_pow_left hG _
          _ = (Nat.card D.Component ^ 3) ^ Nat.card D.Points * Nat.card D.Top ^ 3 := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm (Nat.card D.Points) 3, pow_mul]
          _ ≤ (24 ^ (Nat.card D.Fibre - 1)) ^ Nat.card D.Points *
              24 ^ (Nat.card D.Points - 1) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hC _) hT
          _ = 24 ^ (n - 1) := by
            rw [← pow_mul, ← pow_add]
            congr 1
            have hprod := D.degree_product
            have hr := D.degrees_ge_two.1
            have hs := D.degrees_ge_two.2
            rw [hcard] at hprod
            have he : (Nat.card D.Fibre - 1) * Nat.card D.Points +
                Nat.card D.Points = n := by
              calc
                _ = (Nat.card D.Fibre - 1 + 1) * Nat.card D.Points := by ring
                _ = Nat.card D.Fibre * Nat.card D.Points := by
                  rw [Nat.sub_add_cancel (by omega)]
                _ = n := hprod
            omega

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

abbrev OrbitIndex := MulAction.orbitRel.Quotient G X

abbrev orbitImage (o : OrbitIndex (G := G) (X := X)) :=
  (MulAction.toPermHom G o.orbit).range

def orbitImagesHom : G →* ∀ o : OrbitIndex (G := G) (X := X), orbitImage o where
  toFun g o := (MulAction.toPermHom G o.orbit).rangeRestrict g
  map_one' := by funext o; exact map_one _
  map_mul' g h := by funext o; exact map_mul _ g h

omit [Finite G] [Finite X] in
theorem orbitImagesHom_injective [FaithfulSMul G X] :
    Function.Injective (orbitImagesHom (G := G) (X := X)) := by
  intro g h he
  apply eq_of_smul_eq_smul (α := X)
  intro x
  let o : OrbitIndex (G := G) (X := X) := Quotient.mk'' x
  let v : o.orbit := ⟨x, MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩
  exact congrArg (fun z : ∀ o : OrbitIndex (G := G) (X := X), orbitImage o =>
    ((z o).val v).val) he

omit [Finite G] in
theorem arbitrary_order
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hstructure : PrimitiveSocleRawStructure.PublishedONanScottStructure)
    [FaithfulSMul G X] [IsSolvable G] : Nat.card G ^ 3 ≤ 24 ^ Nat.card X := by
  let O := OrbitIndex (G := G) (X := X)
  letI : Fintype O := Fintype.ofFinite O
  letI (o : O) : Fintype o.orbit := Fintype.ofFinite _
  letI (o : O) : Fintype (orbitImage o) := Fintype.ofFinite _
  have hfactor (o : O) : Nat.card (orbitImage o) ^ 3 ≤ 24 ^ Nat.card o.orbit := by
    letI : Nonempty o.orbit := ⟨⟨o.out,
      MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' o)⟩⟩
    letI : IsSolvable (orbitImage o) := solvable_of_surjective
      (f := (MulAction.toPermHom G o.orbit).rangeRestrict)
      (MulAction.toPermHom G o.orbit).rangeRestrict_surjective
    letI : MulAction.IsPretransitive (orbitImage o) o.orbit := ⟨by
      intro x y
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
      exact ⟨(MulAction.toPermHom G o.orbit).rangeRestrict g, hg⟩⟩
    exact (transitive_order catalogue hstructure (orbitImage o) o.orbit).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  have hcard : ∑ o : O, Nat.card o.orbit = Nat.card X := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma] using
      (Nat.card_congr (MulAction.selfEquivSigmaOrbits' G X)).symm
  have hG : Nat.card G ≤ ∏ o : O, Nat.card (orbitImage o) := by
    have h := Nat.card_le_card_of_injective
      (orbitImagesHom (G := G) (X := X)) orbitImagesHom_injective
    rwa [Nat.card_pi] at h
  calc
    Nat.card G ^ 3 ≤ (∏ o : O, Nat.card (orbitImage o)) ^ 3 :=
      Nat.pow_le_pow_left hG _
    _ = ∏ o : O, Nat.card (orbitImage o) ^ 3 := by
      rw [Finset.prod_pow]
    _ ≤ ∏ o : O, 24 ^ Nat.card o.orbit := Finset.prod_le_prod
      (fun _ _ => Nat.zero_le _) (fun o _ => hfactor o)
    _ = 24 ^ Nat.card X := by rw [Finset.prod_pow_eq_pow_sum, hcard]

/-- The standalone Dixon input is a consequence of the retained primitive
structure, bounded catalogue, and elementary affine linear-map count. -/
theorem dixonOrder_of_primitive_inputs
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hstructure : PrimitiveSocleRawStructure.PublishedONanScottStructure)
    :
    MarkedC4.SolubleContainerOrder.PublishedDixonOrder := by
  intro X _ H _
  have hc := arbitrary_order (G := H) (X := X) catalogue hstructure
  have hc' : Nat.card H ^ 3 ≤ 24 ^ Fintype.card X := by
    simpa only [Nat.card_eq_fintype_card] using hc
  have hreal : (Nat.card H : ℝ) ^ 3 ≤ (24 : ℝ) ^ Fintype.card X := by
    exact_mod_cast hc'
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity)
    (by decide : (3 : ℕ) ≠ 0)).mp
  have htarget : ((24 : ℝ) ^ ((Fintype.card X : ℝ) / 3)) ^ 3 =
      (24 : ℝ) ^ Fintype.card X := by
    rw [← Real.rpow_natCast (24 ^ ((Fintype.card X : ℝ) / 3)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 24)]
    norm_num only [Nat.cast_ofNat]
    rw [show ((Fintype.card X : ℝ) / 3) * (3 : ℝ) =
      (Fintype.card X : ℝ) by ring]
    exact Real.rpow_natCast _ _
  rw [htarget]
  exact hreal

end SymmetricSubgroupAsymptotics.ElementaryDixonOrderProof
