import SymmetricSubgroupAsymptotics.TernaryFourBlockParityModels
import SymmetricSubgroupAsymptotics.BinaryPermutationSemidirectGeneration

/-! Generation of the actual signed four-block sources by one ternary
translation, the block rotation, one sign flip, and (when present) the
block reflection. Only the two kernel coordinate decompositions are used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryFourBlockParityGeneration

open SemidirectProduct
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block Translation)
open BinaryPermutationSemidirectNormalGenerators (Vector CyclicModel DihedralModel cyclicLabels dihedralLabels)
open TernaryFourBlockParityModels
open BinaryPermutationSemidirectGeneration (delta)

abbrev CyclicAffine := LinearSemidirectCoprimeSocleBounds.Model cyclicAction
abbrev DihedralAffine (q : Vector →ₗ[ZMod 2] Vector)
    (hq : ∀ g v, q (BinaryPermutationSemidirectNormalGenerators.linearAction dihedralLabels g v) =
      BinaryPermutationSemidirectNormalGenerators.linearAction dihedralLabels g (q v)) :=
  LinearSemidirectCoprimeSocleBounds.Model (dihedralAction q hq)

def cyclicBaseMap : PrimitiveAffineDegreeTwoTwelveRow131AffineModel.Model →* CyclicAffine :=
  SemidirectProduct.map (MonoidHom.id Translation) (inr : Block →* CyclicModel) (by
    intro c
    apply MonoidHom.ext
    intro v
    apply Multiplicative.toAdd.injective
    exact (congrArg (fun rho : Representation (ZMod 3) Block (Block → ZMod 3) ↦ rho c v.toAdd)
      cyclic_representation_comp).symm)

def dihedralBaseMap (q : Vector →ₗ[ZMod 2] Vector)
    (hq : ∀ g v, q (BinaryPermutationSemidirectNormalGenerators.linearAction dihedralLabels g v) =
      BinaryPermutationSemidirectNormalGenerators.linearAction dihedralLabels g (q v)) :
    PrimitiveAffineDegreeTwoTwelveRow131AffineModel.Model →* DihedralAffine q hq :=
  SemidirectProduct.map (MonoidHom.id Translation)
    ((inr : TernaryFourBlockMetacyclicModel.Complement true →* DihedralModel).comp
      (inl : Block →* TernaryFourBlockMetacyclicModel.Complement true)) (by
        intro c
        apply MonoidHom.ext
        intro v
        apply Multiplicative.toAdd.injective
        exact (congrArg (fun rho : Representation (ZMod 3) Block (Block → ZMod 3) ↦ rho c v.toAdd)
          (dihedral_representation_comp q hq)).symm)

private theorem base_image_mem {G : Type} [Group G]
    (f : PrimitiveAffineDegreeTwoTwelveRow131AffineModel.Model →* G) (D : Subgroup G)
    (h : ∀ i : Fin 2, f (PrimitiveAffineDegreeTwoTwelveRow131AffineModel.modelGenerators i) ∈ D)
    (x : PrimitiveAffineDegreeTwoTwelveRow131AffineModel.Model) : f x ∈ D := by
  have hle : Subgroup.closure
      (Set.range PrimitiveAffineDegreeTwoTwelveRow131AffineModel.modelGenerators) ≤ D.comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  apply hle
  rw [PrimitiveAffineDegreeTwoTwelveRow131AffineModel.model_generated]
  exact Subgroup.mem_top x

def cyclicGenerators : Fin 3 → CyclicAffine :=
  ![cyclicBaseMap (PrimitiveAffineDegreeTwoTwelveRow131AffineModel.modelGenerators 0),
    cyclicBaseMap (PrimitiveAffineDegreeTwoTwelveRow131AffineModel.modelGenerators 1),
    inr (inl (delta 0))]

def dihedralGenerators (q : Vector →ₗ[ZMod 2] Vector)
    (hq : ∀ g v, q (BinaryPermutationSemidirectNormalGenerators.linearAction dihedralLabels g v) =
      BinaryPermutationSemidirectNormalGenerators.linearAction dihedralLabels g (q v)) :
    Fin 4 → DihedralAffine q hq :=
  ![dihedralBaseMap q hq (PrimitiveAffineDegreeTwoTwelveRow131AffineModel.modelGenerators 0),
    dihedralBaseMap q hq (PrimitiveAffineDegreeTwoTwelveRow131AffineModel.modelGenerators 1),
    inr (inl (delta 0)), inr (inr (inr (Multiplicative.ofAdd 1)))]

theorem cyclic_generated : Subgroup.closure (Set.range cyclicGenerators) = ⊤ := by
  let D : Subgroup CyclicAffine := Subgroup.closure (Set.range cyclicGenerators)
  have hbase (x : PrimitiveAffineDegreeTwoTwelveRow131AffineModel.Model) : cyclicBaseMap x ∈ D := by
    apply base_image_mem cyclicBaseMap D ?_ x
    intro i
    fin_cases i
    · exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 3))
    · exact Subgroup.subset_closure (Set.mem_range_self (1 : Fin 3))
  have hright (r : CyclicModel) : (inr r : CyclicAffine) ∈ D := by
    apply BinaryPermutationSemidirectGeneration.image_mem_of_delta_and_base cyclicLabels
      (Multiplicative.ofAdd 1) (by decide +kernel) inr D ?_ ?_ r
    · exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 3))
    · intro c
      exact hbase (inr c)
  apply top_unique
  intro g _
  rw [← inl_left_mul_inr_right g]
  exact D.mul_mem (hbase (inl g.left)) (hright g.right)

theorem dihedral_generated (q : Vector →ₗ[ZMod 2] Vector)
    (hq : ∀ g v, q (BinaryPermutationSemidirectNormalGenerators.linearAction dihedralLabels g v) =
      BinaryPermutationSemidirectNormalGenerators.linearAction dihedralLabels g (q v)) :
    Subgroup.closure (Set.range (dihedralGenerators q hq)) = ⊤ := by
  let D : Subgroup (DihedralAffine q hq) := Subgroup.closure (Set.range (dihedralGenerators q hq))
  have hbase (x : PrimitiveAffineDegreeTwoTwelveRow131AffineModel.Model) :
      dihedralBaseMap q hq x ∈ D := by
    apply base_image_mem (dihedralBaseMap q hq) D ?_ x
    intro i
    fin_cases i
    · exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 4))
    · exact Subgroup.subset_closure (Set.mem_range_self (1 : Fin 4))
  have hbit (b : TernaryFourBlockMetacyclicModel.Bit) :
      (inr (inr (inr b)) : DihedralAffine q hq) ∈ D := by
    have hb : (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.toAdd.val = b := by
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    rw [← hb, map_pow, map_pow, map_pow]
    exact D.pow_mem (Subgroup.subset_closure (Set.mem_range_self (3 : Fin 4))) _
  have hquotient (r : TernaryFourBlockMetacyclicModel.Complement true) :
      (inr (inr r) : DihedralAffine q hq) ∈ D := by
    rw [← inl_left_mul_inr_right r, map_mul, map_mul]
    exact D.mul_mem (hbase (inr r.left)) (hbit r.right)
  have hright (r : DihedralModel) : (inr r : DihedralAffine q hq) ∈ D := by
    apply BinaryPermutationSemidirectGeneration.image_mem_of_delta_and_base dihedralLabels
      (inl (Multiplicative.ofAdd 1)) (by decide +kernel) inr D ?_ hquotient r
    exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 4))
  apply top_unique
  intro g _
  rw [← inl_left_mul_inr_right g]
  exact D.mul_mem (hbase (inl g.left)) (hright g.right)

end TernaryFourBlockParityGeneration
end SymmetricSubgroupAsymptotics

end
