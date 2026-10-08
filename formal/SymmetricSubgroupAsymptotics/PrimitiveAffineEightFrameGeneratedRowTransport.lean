import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedTopTable

/-!
# Generic transport of one generated eight-frame row

This is the proof shared by every row in a generated top table.  It moves
the stored point stabilizer, Schreier transversal and induced binary module
to the literal affine block action, then imports the checked top and module
registries.  Row files only instantiate `GeneratedTopData` and
`GeneratedRowData`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace GeneratedRowData

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance generatedRowTransportPrimeFact : Fact P.p.Prime :=
  (chart block P).primeFact

/-- One shared top bound to the literal block action.  Defining the top
match from these fields keeps its literal action definitionally equal to
the stored action, avoiding any casts between subgroup types. -/
structure BoundTopData
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) : Type 1 where
  top : GeneratedTopData
  pointEquiv : block.Points ≃ Fin 8
  conjugator : Equiv.Perm (Fin 8)
  conjugated :
    MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
      top.literalAction

namespace BoundTopData

def topMatch
    (B : BoundTopData block) :
    DegreeFourZeroCoreEightLiteralTopMatch block B.top.ModelGroup :=
  B.top.literalTopMatch block B.pointEquiv B.conjugator B.conjugated

end BoundTopData

/-- Move the stored point stabilizer into the actual complement quotient. -/
noncomputable def sourceStabilizerToActual
    (B : BoundTopData block)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    B.top.sourceStabilizer ≃*
      fullFrameInducedStabilizer block P
        (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
          (block := block) B.topMatch (0 : Fin 8)) :=
  B.top.sourceStabilizerEquivLiteral.trans
    (fullFrameInducedStabilizerEquivLiteral block P
      B.topMatch hr hD (0 : Fin 8)).symm

theorem fullFrameInducedStabilizerEquivLiteral_sourceStabilizerToActual
    (B : BoundTopData block)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (h : B.top.sourceStabilizer) :
    fullFrameInducedStabilizerEquivLiteral block P B.topMatch hr hD
        (0 : Fin 8)
        (sourceStabilizerToActual block P B hr hD h) =
      B.top.sourceStabilizerEquivLiteral h := by
  change (fullFrameInducedStabilizerEquivLiteral block P B.topMatch hr hD
      (0 : Fin 8))
      (((fullFrameInducedStabilizerEquivLiteral block P B.topMatch hr hD
        (0 : Fin 8)).symm) (B.top.sourceStabilizerEquivLiteral h)) = _
  exact (fullFrameInducedStabilizerEquivLiteral block P B.topMatch hr hD
    (0 : Fin 8)).apply_symm_apply _

theorem groupEquiv_sourceStabilizerToActual
    (B : BoundTopData block)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (h : B.top.sourceStabilizer) :
    DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
        (block := block) (P := P) B.topMatch hr hD
        ((sourceStabilizerToActual block P B hr hD h).1) = h.1 := by
  have hrestrict := groupEquiv_stabilizer block P B.topMatch hr hD
    (0 : Fin 8) (sourceStabilizerToActual block P B hr hD h)
  calc
    DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
        (block := block) (P := P) B.topMatch hr hD
        ((sourceStabilizerToActual block P B hr hD h).1) =
      B.top.actionModelEquiv
        ((fullFrameInducedStabilizerEquivLiteral block P B.topMatch hr hD
          (0 : Fin 8)
          (sourceStabilizerToActual block P B hr hD h)).1) := hrestrict
    _ = B.top.actionModelEquiv (B.top.sourceStabilizerEquivLiteral h).1 := by
      rw [fullFrameInducedStabilizerEquivLiteral_sourceStabilizerToActual
        block P B hr hD h]
    _ = h.1 := B.top.sourceStabilizerEquivLiteral_model h

/-- The actual stabilizer component written in the row's retained local
target. -/
noncomputable def actualLocalMap
    (B : BoundTopData block) (R : GeneratedRowData B.top)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (M : DegreeEightLiteralLocalRowCatalogue.ActualMatch block P B.topMatch
      (R.literalLocalRow B.top) hr hD) :
    fullFrameInducedStabilizer block P
        (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
          (block := block) B.topMatch (0 : Fin 8)) →* R.LocalTarget :=
  M.targetEquiv.toMonoidHom.comp
    (binaryAffineStabilizerComponent block P
      (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
        (block := block) B.topMatch (0 : Fin 8)))

@[simp] theorem actualLocalMap_sourceStabilizerToActual
    (B : BoundTopData block) (R : GeneratedRowData B.top)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (M : DegreeEightLiteralLocalRowCatalogue.ActualMatch block P B.topMatch
      (R.literalLocalRow B.top) hr hD)
    (h : B.top.sourceStabilizer) :
    actualLocalMap block P B R hr hD M
        (sourceStabilizerToActual block P B hr hD h) =
      R.sourceLocalMap h := by
  let L := M.toPointedLocalMatch block P
  have hcomponent := pointedLocalMatch_actual_component block P L
    (sourceStabilizerToActual block P B hr hD h)
  calc
    actualLocalMap block P B R hr hD M
        (sourceStabilizerToActual block P B hr hD h) =
      R.literalLocalMap B.top
        (fullFrameInducedStabilizerEquivLiteral block P B.topMatch hr hD
          (0 : Fin 8)
          (sourceStabilizerToActual block P B hr hD h)) := hcomponent
    _ = R.literalLocalMap B.top (B.top.sourceStabilizerEquivLiteral h) := by
      rw [fullFrameInducedStabilizerEquivLiteral_sourceStabilizerToActual
        block P B hr hD h]
    _ = R.sourceLocalMap h := by
      simp [literalLocalMap]

abbrev ModelModuleAt (p : ℕ) := Fin 16 → ZMod p

abbrev LocalPlaneAt (p : ℕ) := Fin 2 → ZMod p

/-- Characteristic-transported local representation. -/
noncomputable def localRepresentationAt
    (T : GeneratedTopData) (R : GeneratedRowData T)
    {p : ℕ} [Fact p.Prime] (hp : p = 2) :
    Representation (ZMod p) R.LocalTarget (LocalPlaneAt p) := by
  subst p
  exact R.localRepresentation

theorem localRepresentationAt_injective
    (T : GeneratedTopData) (R : GeneratedRowData T)
    {p : ℕ} [Fact p.Prime] (hp : p = 2) :
    Function.Injective (localRepresentationAt T R hp) := by
  subst p
  exact R.localRepresentation_injective

/-- Characteristic-transported sixteen-coordinate model representation. -/
noncomputable def modelRepresentationAt
    (T : GeneratedTopData) (R : GeneratedRowData T)
    {p : ℕ} [Fact p.Prime] (hp : p = 2) :
    Representation (ZMod p) T.ModelGroup (ModelModuleAt p) := by
  subst p
  exact R.modelRepresentation

theorem modelRepresentationAt_generator_formula
    (T : GeneratedTopData) (R : GeneratedRowData T)
    {p : ℕ} [Fact p.Prime] (hp : p = 2)
    (j : T.GeneratorIndex) (v : ModelModuleAt p)
    (a : Fin 8) (i : Fin 2) :
    modelRepresentationAt T R hp (T.ambient j) v
        (CoinducedLeadingCoordinates.label a i) =
      localRepresentationAt T R hp (R.sourceLocalMap (T.twist j a))
        (fun q ↦ v (CoinducedLeadingCoordinates.label (T.next j a) q)) i := by
  subst p
  exact R.modelRepresentation_generator_formula j v a i

theorem modelModuleAt_finrank_eq_sixteen
    {p : ℕ} [Fact p.Prime] :
    Module.finrank (ZMod p) (ModelModuleAt p) = 16 := by
  simp [ModelModuleAt]

noncomputable def modelModuleRegistryAt
    (T : GeneratedTopData) (R : GeneratedRowData T)
    {p : ℕ} [Fact p.Prime] (hp : p = 2) :
    FiniteFrameModuleCyclicOrbitDisplacementRegistry
      (modelRepresentationAt T R hp) 2 := by
  subst p
  exact R.moduleRegistry

/-- Bind one generated row to an arbitrary literal zero-core eight-block
action.  All group-theoretic and module-theoretic finite checks enter only
through `T` and `R`; this proof is shared by every catalogue row. -/
noncomputable def toSelectedRow
    (B : BoundTopData block) (R : GeneratedRowData B.top)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (M : DegreeEightLiteralLocalRowCatalogue.ActualMatch block P B.topMatch
      (R.literalLocalRow B.top) hr hD) :
    DegreeFourZeroCoreEightSelectedRow block P B.topMatch hr hD := by
  let T := B.top
  let topMatch := B.topMatch
  have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
  let point := DegreeFourZeroCoreEightLiteralTopMatch.pointOver
    (block := block) topMatch (0 : Fin 8)
  let H := fullFrameInducedStabilizer block P point
  let rho := fullFrameInducedLocalRepresentation block P point
  let L := M.toPointedLocalMatch block P
  let e := DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
    (block := block) (P := P) topMatch hr hD
  let sourceToActual := sourceStabilizerToActual block P B hr hD
  let actualRepresentative : Fin 8 → DegreeFourComplementQuotient block P :=
    fun a ↦ e.symm (T.representative a)
  let actualGenerator : T.GeneratorIndex → DegreeFourComplementQuotient block P :=
    fun j ↦ e.symm (T.ambient j)
  let actualTwist : T.GeneratorIndex → Fin 8 → H :=
    fun j a ↦ sourceToActual (T.twist j a)
  have hsource (h : T.sourceStabilizer) :
      e (sourceToActual h).1 = h.1 := by
    exact groupEquiv_sourceStabilizerToActual block P B hr hD h
  have hrepresentative (a : Fin 8) :
      e (actualRepresentative a) = T.representative a := by
    exact e.apply_symm_apply _
  have hgenerator (j : T.GeneratorIndex) :
      e (actualGenerator j) = T.ambient j := by
    exact e.apply_symm_apply _
  have hmul (j : T.GeneratorIndex) (a : Fin 8) :
      actualRepresentative a * actualGenerator j =
        (actualTwist j a : DegreeFourComplementQuotient block P) *
          actualRepresentative (T.next j a) := by
    apply e.injective
    rw [map_mul, map_mul, hrepresentative, hgenerator, hrepresentative]
    rw [hsource]
    exact T.representative_mul_generator j a
  have hgenerates : Subgroup.closure (Set.range actualGenerator) = ⊤ := by
    calc
      Subgroup.closure (Set.range actualGenerator) =
          Subgroup.map e.symm.toMonoidHom
            (Subgroup.closure (Set.range T.ambient)) := by
        rw [MonoidHom.map_closure]
        congr 1
        ext x
        simp [actualGenerator, e]
      _ = Subgroup.map e.symm.toMonoidHom ⊤ := by rw [T.ambient_full]
      _ = ⊤ := Subgroup.map_top_of_surjective _ e.symm.surjective
  have hfactor : ∀ x : DegreeFourComplementQuotient block P,
      ∃ h : DegreeFourComplementQuotient block P, h ∈ H ∧
        ∃ a : Fin 8, x = h * actualRepresentative a := by
    intro x
    obtain ⟨h, hh, a, ha⟩ := T.representative_factor (e x)
    let hActual := sourceToActual ⟨h, hh⟩
    refine ⟨hActual.1, hActual.2, a, ?_⟩
    apply e.injective
    rw [map_mul, hsource, hrepresentative]
    exact ha
  let sigma := (localRepresentationAt T R hp).comp
    (actualLocalMap block P B R hr hD M)
  let localEquiv : rho.Equiv sigma := by
    exact pointedInducedLocalEquiv block P L
      (localRepresentationAt T R hp)
      (localRepresentationAt_injective T R hp)
  let basis := Pi.basisFun (ZMod P.p) (Fin 2)
  let coordinateMap := EightFrameInducedCoordinates.coordinatesOfLocalEquiv
    H rho sigma localEquiv actualRepresentative basis
  have coordinateMap_injective : Function.Injective coordinateMap :=
    EightFrameInducedCoordinates.coordinatesOfLocalEquiv_injective
      H rho sigma localEquiv actualRepresentative basis hfactor
  let inducedMatch := DegreeFourZeroCoreEightInducedRowMatch.ofGeneratorEquations
    block P (modelRepresentationAt T R hp) e point actualGenerator hgenerates
    coordinateMap coordinateMap_injective (by
      intro j v
      funext z
      obtain ⟨⟨a, i⟩, rfl⟩ :=
        (finProdFinEquiv (m := 8) (n := 2)).surjective z
      calc
        coordinateMap
            ((Representation.ind H.subtype rho) (actualGenerator j) v)
            (CoinducedLeadingCoordinates.label a i) =
          basis.equivFun
            (sigma (actualTwist j a)
              (((inducedToCoinducedEquiv H sigma)
                ((EightFrameInducedCoordinates.inducedEquivOfLocalEquiv
                  H rho sigma localEquiv) v)).1
                (actualRepresentative (T.next j a)))) i := by
            exact EightFrameInducedCoordinates.coordinatesOfLocalEquiv_action_label
              H rho sigma localEquiv actualRepresentative basis v
              (actualGenerator j) a (T.next j a) (actualTwist j a)
              (hmul j a) i
        _ = localRepresentationAt T R hp
              (R.sourceLocalMap (T.twist j a))
              (fun q ↦ coordinateMap v
                (CoinducedLeadingCoordinates.label (T.next j a) q)) i := by
            rw [Pi.basisFun_equivFun]
            change localRepresentationAt T R hp
              (actualLocalMap block P B R hr hD M
                  (sourceToActual (T.twist j a))) _ i = _
            apply congrArg (fun u : LocalPlaneAt P.p ↦ u i)
            apply congrArg₂
              (fun g u ↦ localRepresentationAt T R hp g u)
            · exact actualLocalMap_sourceStabilizerToActual
                block P B R hr hD M (T.twist j a)
            · funext q
              have hcoordinate :=
                EightFrameInducedCoordinates.coordinatesOfLocalEquiv_label
                  H rho sigma localEquiv actualRepresentative basis v
                    (T.next j a) q
              simpa only [Pi.basisFun_equivFun,
                LinearEquiv.refl_apply] using hcoordinate.symm
        _ = modelRepresentationAt T R hp (T.ambient j) (coordinateMap v)
              (CoinducedLeadingCoordinates.label a i) :=
            (modelRepresentationAt_generator_formula T R hp j
              (coordinateMap v) a i).symm
        _ = modelRepresentationAt T R hp (e (actualGenerator j))
              (coordinateMap v)
              (CoinducedLeadingCoordinates.label a i) := by rw [hgenerator])
  exact {
    ModelModule := ModelModuleAt P.p
    representation := modelRepresentationAt T R hp
    inducedEmbedding := inducedMatch.inducedEmbedding
    inducedEmbedding_injective := inducedMatch.inducedEmbedding_injective
    model_finrank_eq_sixteen := modelModuleAt_finrank_eq_sixteen
    classCount := T.classCount
    representative := T.conjugacyRepresentative
    conjugacyCover := T.conjugacyCover
    TopIndex := T.TopIndex
    AmbientIndex := T.GeneratorIndex
    GeneratorIndex := T.NormalGeneratorIndex
    ambient := T.ambient
    stateGenerators := T.stateGenerators
    top := T.topRegistry
    moduleRegistry := modelModuleRegistryAt T R hp }

/-- Public five-slot capacity row obtained from the generic transport. -/
noncomputable def boundsOfActualMatch
    (B : BoundTopData block) (R : GeneratedRowData B.top)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (M : DegreeEightLiteralLocalRowCatalogue.ActualMatch block P B.topMatch
      (R.literalLocalRow B.top) hr hD)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 := by
  let C := elementaryChart block P
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V ↦ C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  exact (toSelectedRow block P B R hr hD M).toBounds block P hs

end GeneratedRowData

namespace GeneratedTopTable

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Select the actual local quotient from the complete dependent table and
apply the single generic row-transport theorem.  This replaces every
handwritten per-row `ActualBinding` proof. -/
noncomputable def bounds
    (T : GeneratedTopData) (C : GeneratedTopTable T)
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        T.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 := by
  let B : GeneratedRowData.BoundTopData block :=
    ⟨T, pointEquiv, conjugator, hconjugated⟩
  let topMatch := B.topMatch
  obtain ⟨r, M⟩ :=
    (C.localCatalogue T).selectActualExact block P topMatch hr hD
  exact GeneratedRowData.boundsOfActualMatch
    block P B (C.data r) hr hD M hs

end GeneratedTopTable
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
