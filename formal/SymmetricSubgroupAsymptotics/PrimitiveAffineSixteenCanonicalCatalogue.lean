import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop1CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop2CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop3CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop4CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop5CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop6CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop7CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop8CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop9CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop10CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop11CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop12CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop13CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop14CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop15CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop16CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop17CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop18CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop19CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop20CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenLiteralFrameTransport

/-! Exact primitive degree-sixteen catalogue correspondence. The first
twenty entries are the displayed affine representatives of pinned
PrimGrp3.4.4; the last two are the natural A16 and S16 actions. Published
primitive classification is stated only for this fixed canonical family.
All project-owned transfers to the retained original generators are
proved from the selected bidirectional point-word certificates. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveSixteenCanonicalCatalogue
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def canonical : Fin 22 → Subgroup (Equiv.Perm (Fin 16)) :=
  ![PrimitiveAffineSixteenTop1CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop2CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop3CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop4CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop5CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop6CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop7CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop8CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop9CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop10CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop11CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop12CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop13CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop14CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop15CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop16CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop17CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop18CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop19CatalogueBinding.catalogueAction,
    PrimitiveAffineSixteenTop20CatalogueBinding.catalogueAction,
    alternatingGroup (Fin 16), ⊤]

def conjugator : Fin 22 → Equiv.Perm (Fin 16) :=
  ![PrimitiveAffineSixteenTop1CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop2CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop3CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop4CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop5CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop6CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop7CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop8CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop9CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop10CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop11CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop12CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop13CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop14CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop15CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop16CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop17CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop18CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop19CatalogueBinding.conjugator,
    PrimitiveAffineSixteenTop20CatalogueBinding.conjugator, 1, 1]

theorem literal_conjugated_eq (j : Fin 22) :
    MulAut.conj (conjugator j) • PrimitiveAffineSixteenAllLiteralFrames.top j =
      canonical j := by
  fin_cases j
  · exact PrimitiveAffineSixteenTop1CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop2CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop3CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop4CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop5CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop6CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop7CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop8CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop9CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop10CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop11CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop12CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop13CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop14CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop15CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop16CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop17CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop18CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop19CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineSixteenTop20CatalogueBinding.literal_conjugated_eq
  · change MulAut.conj (1 : Equiv.Perm (Fin 16)) • alternatingGroup (Fin 16) = _
    simp [canonical]
  · change MulAut.conj (1 : Equiv.Perm (Fin 16)) • (⊤ : Subgroup (Equiv.Perm (Fin 16))) = _
    simp [canonical]

/-- The published primitive-degree-sixteen classification, specialized
to the twenty fixed PrimGrp affine representatives and the two standard
natural actions. No eligibility, original-row bound, project ownership
predicate or arbitrary family is part of this literature boundary. -/
def PublishedClassification : Prop :=
  ∀ T : Subgroup (Equiv.Perm (Fin 16)),
    MulAction.IsPreprimitive T (Fin 16) →
      ∃ (j : Fin 22) (g : Equiv.Perm (Fin 16)), MulAut.conj g • T = canonical j

theorem originalClassification (published : PublishedClassification)
    (T : Subgroup (Equiv.Perm (Fin 16)))
    (hprimitive : MulAction.IsPreprimitive T (Fin 16)) :
    ∃ (j : Fin 22) (g : Equiv.Perm (Fin 16)),
      MulAut.conj g • T = PrimitiveAffineSixteenAllLiteralFrames.top j := by
  obtain ⟨j, g, hg⟩ := published T hprimitive
  refine ⟨j, (conjugator j)⁻¹ * g, ?_⟩
  rw [map_mul, mul_smul, hg, ← literal_conjugated_eq j, ← mul_smul, ← map_mul]
  simp

/-- Locate an arbitrary original primitive action, retaining its actual
point chart rather than only its group order or abstract isomorphism. -/
def primitiveLiteralMatch (published : PublishedClassification)
    {X : Type} [Finite X] (S : Subgroup (Equiv.Perm X))
    [MulAction.IsPreprimitive S X] (hX : Nat.card X = 16) :
    PrimitiveAffineSixteenAllLiteralFrames.LiteralMatch S := by
  let points : X ≃ Fin 16 := Finite.equivFinOfCardEq hX
  let T := relabelSubgroup points S
  let eG : S ≃* T := points.permCongrHom.subgroupMap S
  let f : MulActionHom eG X (Fin 16) := {
    toFun := points
    map_smul' := by
      intro s x
      change points (s.1 x) = ((points.permCongrHom.subgroupMap S s).1) (points x)
      simp [Equiv.permCongr_apply] }
  have hprimitive : MulAction.IsPreprimitive T (Fin 16) :=
    MulAction.IsPreprimitive.of_surjective (f := f) points.surjective
  let selected := originalClassification published T hprimitive
  let j := Classical.choose selected
  let selectedConjugator := Classical.choose_spec selected
  let g := Classical.choose selectedConjugator
  exact {
    index := j
    points := points
    conjugator := g
    matched := Classical.choose_spec selectedConjugator }

end SymmetricSubgroupAsymptotics.PrimitiveSixteenCanonicalCatalogue
end
