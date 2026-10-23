import SymmetricSubgroupAsymptotics.CFSGFFourE6GoodSylow

/-! A named actual Sylow of the folded F4 matrix group is exactly its
intersection with E6 U. This exposes the existing regular-element Sylow
argument without any group-order formula or fixed-positive cardinality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveSylow
open CFSGFFourSerreMatrices CFSGFFourE6GoodSylow CFSGFFourE6RootSubgroups
open CFSGFFourE6RegularPositive CFSGFFourE6AmbientPositiveSylow
open CFSGRegularElementSylowIntersection CFSGSerreQuadraticMatrix

private def intersectionPositiveSylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Sylow p (FoldedInAmbient K) :=
  intersectionSylow (ambientSylow K p) (FoldedInAmbient K) (regularAmbient K)
    (regularAmbient_positive K) (foldedRegular_mem K) (regularAmbient_unique K)

def positiveSylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Sylow p (canonicalElementaryGroup realizationData K) :=
  (intersectionPositiveSylow K p).mapSurjective
    (f := (Subgroup.subgroupOfEquivOfLe (foldedModel_le_ambient K)).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe (foldedModel_le_ambient K)).surjective

theorem positiveSylow_coe (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)) =
      (E6Positive K).subgroupOf (canonicalElementaryGroup realizationData K) := by
  let e := Subgroup.subgroupOfEquivOfLe (foldedModel_le_ambient K)
  change ((intersectionPositiveSylow K p : Subgroup (FoldedInAmbient K)).map e.toMonoidHom) = _
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    let y : FoldedInAmbient K := ⟨⟨x.val,foldedModel_le_ambient K x.property⟩,x.property⟩
    refine ⟨y,?_,?_⟩
    · exact hx
    · apply Subtype.ext
      rfl

end SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveSylow
