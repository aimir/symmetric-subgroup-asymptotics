import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRows10And12BlockImages

/-! The retained row13 contains every full block translation. Its last
generator is supported on one block, its three-cycle supplies the second
local direction, and its two Klein lifts move these directions to all blocks. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRows10To13BlockLifts

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourBlockAugmentation BinaryFourFullBlockCoordinates SemidirectProduct

def row13BlockMove : Fin 4 → Equiv.Perm (Fin 16) :=
  ![1, DegreeTwoZeroSixteenInterfaces.row13Generators 2,
    DegreeTwoZeroSixteenInterfaces.row13Generators 1,
    DegreeTwoZeroSixteenInterfaces.row13Generators 1 *
      DegreeTwoZeroSixteenInterfaces.row13Generators 2]

def row13LocalWord : Fin 2 → Equiv.Perm (Fin 16) :=
  ![DegreeTwoZeroSixteenInterfaces.row13Generators 3,
    conjugateWord (DegreeTwoZeroSixteenInterfaces.row13Generators 0)
      (DegreeTwoZeroSixteenInterfaces.row13Generators 3) *
        (DegreeTwoZeroSixteenInterfaces.row13Generators 3)⁻¹]

def row13BlockWord (b : Fin 4) (j : Fin 2) : Equiv.Perm (Fin 16) :=
  conjugateWord (row13BlockMove b) (row13LocalWord j)

theorem row13BlockWord_eq (b : Fin 4) (j : Fin 2) :
    row13BlockWord b j = translation (Multiplicative.ofAdd (Pi.single b (Pi.single j 1))) := by
  apply Equiv.ext
  intro x
  revert b j x
  decide +kernel

theorem row13BlockWord_mem (b : Fin 4) (j : Fin 2) :
    row13BlockWord b j ∈ DegreeTwoZeroSixteenInterfaces.row13.top := by
  let H := DegreeTwoZeroSixteenInterfaces.row13.top
  have hg (i : Fin 4) : DegreeTwoZeroSixteenInterfaces.row13Generators i ∈ H :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hb (b : Fin 4) : row13BlockMove b ∈ H := by
    fin_cases b
    · exact H.one_mem
    · exact hg 2
    · exact hg 1
    · exact H.mul_mem (hg 1) (hg 2)
  have hj (j : Fin 2) : row13LocalWord j ∈ H := by
    fin_cases j
    · exact hg 3
    · exact H.mul_mem (conjugateWord_mem H (hg 0) (hg 3)) (H.inv_mem (hg 3))
  exact conjugateWord_mem H (hb b) (hj j)

def row13ModuleWord (w : BinaryFourBlockAugmentation.Module) : Equiv.Perm (Fin 16) :=
  row13BlockWord 0 0 ^ (w 0 0).val * row13BlockWord 0 1 ^ (w 0 1).val *
  row13BlockWord 1 0 ^ (w 1 0).val * row13BlockWord 1 1 ^ (w 1 1).val *
  row13BlockWord 2 0 ^ (w 2 0).val * row13BlockWord 2 1 ^ (w 2 1).val *
  row13BlockWord 3 0 ^ (w 3 0).val * row13BlockWord 3 1 ^ (w 3 1).val

theorem row13ModuleWord_mem (w : BinaryFourBlockAugmentation.Module) :
    row13ModuleWord w ∈ DegreeTwoZeroSixteenInterfaces.row13.top := by
  let H := DegreeTwoZeroSixteenInterfaces.row13.top
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
    (H.pow_mem (row13BlockWord_mem 0 0) _) (H.pow_mem (row13BlockWord_mem 0 1) _))
    (H.pow_mem (row13BlockWord_mem 1 0) _)) (H.pow_mem (row13BlockWord_mem 1 1) _))
    (H.pow_mem (row13BlockWord_mem 2 0) _)) (H.pow_mem (row13BlockWord_mem 2 1) _))
    (H.pow_mem (row13BlockWord_mem 3 0) _)) (H.pow_mem (row13BlockWord_mem 3 1) _)

theorem row13_basis_word (i : Fin 8) :
    row13ModuleWord (fullDecode (fullBasis i)) =
      fullTranslations (Multiplicative.ofAdd (fullBasis i)) := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row13_translation_mem (x : FullCoordinates) :
    fullTranslations (Multiplicative.ofAdd x) ∈ DegreeTwoZeroSixteenInterfaces.row13.top := by
  let H := DegreeTwoZeroSixteenInterfaces.row13.top
  have hB (i : Fin 8) : fullTranslations (Multiplicative.ofAdd (fullBasis i)) ∈ H := by
    rw [← row13_basis_word]
    exact row13ModuleWord_mem _
  rw [fullCoordinate_word]
  simp only [map_mul, map_pow]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
    (H.pow_mem (hB 0) _) (H.pow_mem (hB 1) _)) (H.pow_mem (hB 2) _))
    (H.pow_mem (hB 3) _)) (H.pow_mem (hB 4) _)) (H.pow_mem (hB 5) _))
    (H.pow_mem (hB 6) _)) (H.pow_mem (hB 7) _)

theorem row13_range : fullPermutation.range = DegreeTwoZeroSixteenInterfaces.row13.top := by
  apply le_antisymm ?_ row13_top_le_range
  apply range_le_of_kernel_lifts (SemidirectProduct.rightHom : BinaryFourFullBlockCoordinates.Ambient →* Complement)
    fullPermutation DegreeTwoZeroSixteenInterfaces.row13.top
    (row13Lifts 0) (row13Lifts 1) (row13Lifts 2) rfl rfl rfl
  · rw [row13_lifts_original]
    exact Subgroup.subset_closure (Set.mem_range_self 0)
  · rw [row13_lifts_original]
    exact Subgroup.subset_closure (Set.mem_range_self 1)
  · rw [row13_lifts_original]
    exact Subgroup.subset_closure (Set.mem_range_self 2)
  · intro g hg
    have hr : g.right = 1 := hg
    have he : g = inl g.left := SemidirectProduct.ext rfl hr
    rw [he, fullPermutation_inl]
    exact row13_translation_mem g.left.toAdd

def row13Map : BinaryFourFullBlockCoordinates.Ambient →* DegreeTwoZeroSixteenInterfaces.row13.top :=
  fullPermutation.codRestrict _ (fun g => by
    rw [← row13_range]
    exact ⟨g, rfl⟩)

theorem row13Map_surjective : Function.Surjective row13Map := by
  intro y
  have hy : (y : Equiv.Perm (Fin 16)) ∈ fullPermutation.range := by
    rw [row13_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

end PrimitiveAffineDegreeTwoZeroSixteenRows10To13BlockLifts
end SymmetricSubgroupAsymptotics

end
