import SymmetricSubgroupAsymptotics.BinaryFanoHeptadRepresentation
import SymmetricSubgroupAsymptotics.BinaryFanoHeptadNonzeroOrbit
import SymmetricSubgroupAsymptotics.AlternatingSymmetricNormalChain

/-! The original row11/20 complements are surjective images of A8/A7
under the exact heptad representation. These literal range equalities
transport the normal chains. The original row20 nonzero orbit, followed
by inclusion and the explicit row11 chart, proves both irreducibilities. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRows11And20Complements

open BinaryFourAffineImage BinaryFanoHeptadData BinaryFanoHeptadGenerators
open BinaryFanoHeptadRepresentation

abbrev R11 : Subgroup LinearGroup := Subgroup.closure ({a11, b11} : Set LinearGroup)
abbrev R20 : Subgroup LinearGroup := Subgroup.closure ({a20, b20} : Set LinearGroup)

theorem a11_mem : a11 ∈ R11 := Subgroup.subset_closure (by simp)
theorem b11_mem : b11 ∈ R11 := Subgroup.subset_closure (by simp)
theorem a20_mem : a20 ∈ R20 := Subgroup.subset_closure (by simp)
theorem b20_mem : b20 ∈ R20 := Subgroup.subset_closure (by simp)

theorem hom11_range : hom11.range = R11 := by
  rw [MonoidHom.range_eq_map, ← source8_generators, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, hom11_b8, hom11_c8]

theorem hom7_range : hom7.range = R20 := by
  rw [MonoidHom.range_eq_map, ← source7_generators, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, hom7_b7, hom7_a7]
  exact congrArg Subgroup.closure (Set.pair_comm b20 a20)

def complementMap11 : Source8 →* R11 :=
  (MulEquiv.subgroupCongr hom11_range).toMonoidHom.comp hom11.rangeRestrict
def complementMap20 : Source7 →* R20 :=
  (MulEquiv.subgroupCongr hom7_range).toMonoidHom.comp hom7.rangeRestrict

theorem complementMap11_surjective : Function.Surjective complementMap11 :=
  (MulEquiv.subgroupCongr hom11_range).surjective.comp hom11.rangeRestrict_surjective
theorem complementMap20_surjective : Function.Surjective complementMap20 :=
  (MulEquiv.subgroupCongr hom7_range).surjective.comp hom7.rangeRestrict_surjective

theorem linear_normal_total11 (A B : Subgroup R11) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective (G := Source8) (H := R11)
    complementMap11 complementMap11_surjective
    (AlternatingSymmetricNormalChain.alternating_normal_total (X := Fin 8) (by norm_num)) A B hA hB

theorem linear_normal_total20 (A B : Subgroup R20) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective (G := Source7) (H := R20)
    complementMap20 complementMap20_surjective
    (AlternatingSymmetricNormalChain.alternating_normal_total (X := Fin 7) (by norm_num)) A B hA hB

theorem irreducible20 : AffineModel.Irreducible R20 :=
  BinaryFanoHeptadNonzeroOrbit.irreducible R20 a20_mem b20_mem

theorem conjugate_R20_le_R11 : R20.map (MulAut.conj chart11).toMonoidHom ≤ R11 := by
  rintro _ ⟨r, hr, rfl⟩
  rw [← hom7_range] at hr
  obtain ⟨g, rfl⟩ := hr
  change hom11 (include7 g) ∈ R11
  rw [← hom11_range]
  exact ⟨include7 g, rfl⟩

theorem irreducible11 : AffineModel.Irreducible R11 :=
  AffineModel.irreducible_of_conjugate_le R20 R11 chart11 irreducible20 conjugate_R20_le_R11

end PrimitiveAffineDegreeTwoPrimitiveSixteenRows11And20Complements
end SymmetricSubgroupAsymptotics

end
