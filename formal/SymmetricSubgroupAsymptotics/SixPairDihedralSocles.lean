import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.DihedralNormalGenerators

/-! A shared quotient-socle bound for six physical pairs with the actual
dihedral six-point image. The image is covered by an explicit dihedral
homomorphism, whose all-normal two-generator bound is transferred by a
surjection. The cyclic pair-module bound contributes one more generator.
No ambient normal-generator bound is inherited by an arbitrary subgroup. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixPairDihedralSocles

open SixPairCyclicSymmetricSocles

def reflection : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 2, 1, 0]
  invFun := ![5, 4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def tops : Fin 3 → Equiv.Perm (Fin 6) := ![1, cycle, reflection]

def dihedralMap : DihedralGroup 6 →* Equiv.Perm (Fin 6) where
  toFun
    | .r i => cycle ^ i.val
    | .sr i => reflection * cycle ^ i.val
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      apply Equiv.ext <;> intro x <;> revert i j x <;> decide +kernel

theorem dihedralMap_range : dihedralMap.range = Subgroup.closure (Set.range tops) := by
  have hc : cycle ∈ Subgroup.closure (Set.range tops) :=
    Subgroup.subset_closure ⟨1, rfl⟩
  have hs : reflection ∈ Subgroup.closure (Set.range tops) :=
    Subgroup.subset_closure ⟨2, rfl⟩
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    cases g with
    | r i => exact (Subgroup.closure (Set.range tops)).pow_mem hc i.val
    | sr i =>
      exact (Subgroup.closure (Set.range tops)).mul_mem hs
        ((Subgroup.closure (Set.range tops)).pow_mem hc i.val)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨1, rfl⟩
    · exact ⟨DihedralGroup.r 1, by decide +kernel⟩
    · exact ⟨DihedralGroup.sr 0, by decide +kernel⟩

theorem dihedral_normalGen (L : Subgroup dihedralMap.range) (hL : L.Normal) :
    MarkedC4.normalGen L ≤ 2 := by
  letI := hL
  obtain ⟨x, hx⟩ := normal_generating_tuples_of_surjective dihedralMap.rangeRestrict
    dihedralMap.rangeRestrict_surjective (DihedralNormalGenerators.normal_generating_pairs 6) L hL
  exact normalGen_le_of_fin_tuple x hx

theorem quotientSocle {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) (g : U) (hg : F.top g = cycle)
    (himage : F.top.range = dihedralMap.range)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 := by
  apply F.quotientSocle_of_uniform_pair_action 1 2
    (SixPairCyclicSymmetricSocles.uniform F g hg) ?_ N
  intro L hL
  letI := hL
  let e : F.top.range ≃* dihedralMap.range := MulEquiv.subgroupCongr himage
  exact CoprimeKernelQuotientSocles.normalGen_image_bound
    e.symm.toMonoidHom e.symm.surjective 2 dihedral_normalGen L

end SymmetricSubgroupAsymptotics.SixPairDihedralSocles

end
