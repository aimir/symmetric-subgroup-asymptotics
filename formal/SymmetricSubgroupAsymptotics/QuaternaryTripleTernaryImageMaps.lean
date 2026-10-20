import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow94WreathModel

/-! Equivariant images of the actual three-block quaternary model.
The map multiplies the fixed type by `a` and the augmentation type by
`b`. Exact original-generator lifts and image words identify a literal
image; the original quotient map then retains socle bound one. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace QuaternaryTripleTernaryImageMaps

open QuaternaryTernaryInvariantPlane QuaternaryTripleTernaryWreathModel SemidirectProduct

def sumCoordinates (v : Vector) : Scalar :=
  v (Multiplicative.ofAdd 0) + v (Multiplicative.ofAdd 1) + v (Multiplicative.ofAdd 2)

theorem sumCoordinates_rotation (z : Block) (v : Vector) :
    sumCoordinates (linearAction z v) = sumCoordinates v := by
  rcases block_cases z with rfl | rfl | rfl
  · rfl
  · change v (Multiplicative.ofAdd 2) + v (Multiplicative.ofAdd 0) +
      v (Multiplicative.ofAdd 1) = _
    dsimp only [sumCoordinates]
    ac_rfl
  · change v (Multiplicative.ofAdd 1) + v (Multiplicative.ofAdd 2) +
      v (Multiplicative.ofAdd 0) = _
    dsimp only [sumCoordinates]
    ac_rfl

def projection (a b : Scalar) : Vector →ₗ[Scalar] Vector where
  toFun v i := b * v i + 3 * (a - b) * sumCoordinates v
  map_add' v w := by
    funext i
    simp [sumCoordinates]
    ring
  map_smul' c v := by
    funext i
    simp [sumCoordinates]
    ring

theorem projection_rotation (a b : Scalar) (z : Block) (v : Vector) :
    projection a b (linearAction z v) = linearAction z (projection a b v) := by
  funext i
  change b * v (z⁻¹ * i) + 3 * (a - b) * sumCoordinates (linearAction z v) =
    b * v (z⁻¹ * i) + 3 * (a - b) * sumCoordinates v
  rw [sumCoordinates_rotation]

def modelMap (a b : Scalar) : Model →* Model :=
  SemidirectProduct.map (projection a b).toAddMonoidHom.toMultiplicative
    (MonoidHom.id Block) (by
      intro z
      apply MonoidHom.ext
      intro v
      apply Multiplicative.toAdd.injective
      exact projection_rotation a b z v.toAdd)

def literalMap (a b : Scalar) : Model →* Equiv.Perm (Fin 12) :=
  PrimitiveAffineDegreeTwoTwelveRow94WreathModel.literalAction.comp (modelMap a b)

def vector (a b c : Scalar) : Vector := fun i =>
  ![a, b, c] (⟨i.toAdd.val, i.toAdd.val_lt⟩ : Fin 3)

variable (a b : Scalar) {n : ℕ}
  (generators : Fin n → Equiv.Perm (Fin 12)) (lifts : Fin n → Model)
  (hlifts : ∀ i, literalMap a b (lifts i) = generators i)
  (hgenerators : ∀ i : Fin 2, literalMap a b (modelGenerators i) ∈
    Subgroup.closure (Set.range generators))

include hlifts hgenerators

theorem literalMap_range :
    (literalMap a b).range = Subgroup.closure (Set.range generators) := by
  apply le_antisymm
  · have hle : Subgroup.closure (Set.range modelGenerators) ≤
        (Subgroup.closure (Set.range generators)).comap (literalMap a b) := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      exact hgenerators i
    rintro _ ⟨g, rfl⟩
    apply hle
    rw [model_generated]
    exact Subgroup.mem_top g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨lifts i, hlifts i⟩

def modelToTop : Model →* Subgroup.closure (Set.range generators) :=
  (MulEquiv.subgroupCongr (literalMap_range a b generators lifts hlifts hgenerators)).toMonoidHom.comp
    (literalMap a b).rangeRestrict

theorem modelToTop_surjective :
    Function.Surjective (modelToTop a b generators lifts hlifts hgenerators) :=
  (MulEquiv.subgroupCongr (literalMap_range a b generators lifts hlifts hgenerators)).surjective.comp
    (literalMap a b).rangeRestrict_surjective

theorem socle_of_surjective {Q : Type} [Group Q]
    (pi : Subgroup.closure (Set.range generators) →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 1 :=
  QuaternaryTripleTernaryWreathModel.socle_of_surjective
    (pi.comp (modelToTop a b generators lifts hlifts hgenerators))
    (hpi.comp (modelToTop_surjective a b generators lifts hlifts hgenerators))

theorem quotientSocle (N : Subgroup (Subgroup.closure (Set.range generators))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range generators) ⧸ N) 1 :=
  socle_of_surjective a b generators lifts hlifts hgenerators
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end QuaternaryTripleTernaryImageMaps
end SymmetricSubgroupAsymptotics

end
