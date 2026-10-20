import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenRows10To13BlockLifts

/-! Exact reverse range inclusions for the two nonsplit models.
Squares and commutators of the retained lifts generate their full
translation kernels. Only the resulting words on sixteen points are checked. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRows10To13BlockLifts

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourBlockAugmentation BinaryFourFullBlockCoordinates

def conjugateWord (c x : Equiv.Perm (Fin 16)) : Equiv.Perm (Fin 16) := c * x * c⁻¹

theorem conjugateWord_mem (H : Subgroup (Equiv.Perm (Fin 16)))
    {c x : Equiv.Perm (Fin 16)} (hc : c ∈ H) (hx : x ∈ H) : conjugateWord c x ∈ H :=
  H.mul_mem (H.mul_mem hc hx) (H.inv_mem hc)

def row10Square : Equiv.Perm (Fin 16) := DegreeTwoZeroSixteenInterfaces.row10Generators 1 ^ 2
def row10Diagonal : Equiv.Perm (Fin 16) :=
  conjugateWord (DegreeTwoZeroSixteenInterfaces.row10Generators 2) row10Square * row10Square⁻¹
def row10Tail : Equiv.Perm (Fin 16) := row10Square * row10Diagonal⁻¹

def row10BasisWords : Fin 5 → Equiv.Perm (Fin 16) :=
  ![row10Diagonal,
    conjugateWord (DegreeTwoZeroSixteenInterfaces.row10Generators 0) row10Diagonal *
      row10Diagonal⁻¹,
    conjugateWord (DegreeTwoZeroSixteenInterfaces.row10Generators 0)
      (conjugateWord (DegreeTwoZeroSixteenInterfaces.row10Generators 0) row10Tail),
    row10Tail,
    conjugateWord (DegreeTwoZeroSixteenInterfaces.row10Generators 0) row10Tail]

theorem row10BasisWords_eq (i : Fin 5) : row10BasisWords i =
    translations (Multiplicative.ofAdd (basisVector i.castSucc)) := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row10BasisWords_mem (i : Fin 5) :
    row10BasisWords i ∈ DegreeTwoZeroSixteenInterfaces.row10.top := by
  let H := DegreeTwoZeroSixteenInterfaces.row10.top
  have hg (j : Fin 3) : DegreeTwoZeroSixteenInterfaces.row10Generators j ∈ H :=
    Subgroup.subset_closure (Set.mem_range_self j)
  have hs : row10Square ∈ H := H.pow_mem (hg 1) 2
  have hd : row10Diagonal ∈ H :=
    H.mul_mem (conjugateWord_mem H (hg 2) hs) (H.inv_mem hs)
  have ht : row10Tail ∈ H := H.mul_mem hs (H.inv_mem hd)
  have hcd := conjugateWord_mem H (hg 0) hd
  have hct := conjugateWord_mem H (hg 0) ht
  have hcct := conjugateWord_mem H (hg 0) hct
  fin_cases i
  · exact hd
  · exact H.mul_mem hcd (H.inv_mem hd)
  · exact hcct
  · exact ht
  · exact hct

def row12Square : Equiv.Perm (Fin 16) := DegreeTwoZeroSixteenInterfaces.row12Generators 1 ^ 2
def row12Diagonal : Equiv.Perm (Fin 16) :=
  conjugateWord (DegreeTwoZeroSixteenInterfaces.row12Generators 2) row12Square * row12Square⁻¹
def row12DiagonalOne : Equiv.Perm (Fin 16) :=
  conjugateWord (DegreeTwoZeroSixteenInterfaces.row12Generators 0) row12Diagonal
def row12Tail : Equiv.Perm (Fin 16) := row12Square * row12Diagonal⁻¹
def row12TailCycle : Equiv.Perm (Fin 16) :=
  conjugateWord (DegreeTwoZeroSixteenInterfaces.row12Generators 0) row12Tail *
    row12DiagonalOne⁻¹
def row12Trace : Equiv.Perm (Fin 16) := DegreeTwoZeroSixteenInterfaces.row12Generators 0 ^ 3
def row12Fifth : Equiv.Perm (Fin 16) := row12TailCycle * row12Trace⁻¹
def row12Fourth : Equiv.Perm (Fin 16) := row12Tail * row12Fifth⁻¹
def row12Second : Equiv.Perm (Fin 16) :=
  conjugateWord (DegreeTwoZeroSixteenInterfaces.row12Generators 0)
    (conjugateWord (DegreeTwoZeroSixteenInterfaces.row12Generators 0) row12Tail) *
      row12Diagonal⁻¹ * row12Fifth⁻¹

def row12BasisWords : Fin 6 → Equiv.Perm (Fin 16) :=
  ![row12Diagonal * row12DiagonalOne⁻¹, row12DiagonalOne, row12Second,
    row12Trace * row12Second⁻¹ * row12Fourth⁻¹, row12Fourth, row12Fifth]

theorem row12BasisWords_eq (i : Fin 6) : row12BasisWords i =
    translations (Multiplicative.ofAdd (basisVector i)) := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row12BasisWords_mem (i : Fin 6) :
    row12BasisWords i ∈ DegreeTwoZeroSixteenInterfaces.row12.top := by
  let H := DegreeTwoZeroSixteenInterfaces.row12.top
  have hg (j : Fin 3) : DegreeTwoZeroSixteenInterfaces.row12Generators j ∈ H :=
    Subgroup.subset_closure (Set.mem_range_self j)
  have hs : row12Square ∈ H := H.pow_mem (hg 1) 2
  have hd : row12Diagonal ∈ H :=
    H.mul_mem (conjugateWord_mem H (hg 2) hs) (H.inv_mem hs)
  have h1 : row12DiagonalOne ∈ H := conjugateWord_mem H (hg 0) hd
  have ht : row12Tail ∈ H := H.mul_mem hs (H.inv_mem hd)
  have hct : row12TailCycle ∈ H :=
    H.mul_mem (conjugateWord_mem H (hg 0) ht) (H.inv_mem h1)
  have hq : row12Trace ∈ H := H.pow_mem (hg 0) 3
  have h5 : row12Fifth ∈ H := H.mul_mem hct (H.inv_mem hq)
  have h4 : row12Fourth ∈ H := H.mul_mem ht (H.inv_mem h5)
  have h2 : row12Second ∈ H :=
    H.mul_mem (H.mul_mem
      (conjugateWord_mem H (hg 0) (conjugateWord_mem H (hg 0) ht))
      (H.inv_mem hd)) (H.inv_mem h5)
  fin_cases i
  · exact H.mul_mem hd (H.inv_mem h1)
  · exact h1
  · exact h2
  · exact H.mul_mem (H.mul_mem hq (H.inv_mem h2)) (H.inv_mem h4)
  · exact h4
  · exact h5

theorem row10_translation_mem (x : Coordinates) (hx : x 5 = 0) :
    translations (Multiplicative.ofAdd x) ∈ DegreeTwoZeroSixteenInterfaces.row10.top := by
  let H := DegreeTwoZeroSixteenInterfaces.row10.top
  have hB (i : Fin 5) : translations (Multiplicative.ofAdd (basisVector i.castSucc)) ∈ H := by
    rw [← row10BasisWords_eq]
    exact row10BasisWords_mem i
  rw [translation_basis_word, hx]
  simp only [ZMod.val_zero, pow_zero, mul_one]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
    (H.pow_mem (hB 0) _) (H.pow_mem (hB 1) _)) (H.pow_mem (hB 2) _))
      (H.pow_mem (hB 3) _)) (H.pow_mem (hB 4) _)

theorem row12_translation_mem (x : Coordinates) :
    translations (Multiplicative.ofAdd x) ∈ DegreeTwoZeroSixteenInterfaces.row12.top := by
  let H := DegreeTwoZeroSixteenInterfaces.row12.top
  have hB (i : Fin 6) : translations (Multiplicative.ofAdd (basisVector i)) ∈ H := by
    rw [← row12BasisWords_eq]
    exact row12BasisWords_mem i
  rw [translation_basis_word]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
    (H.pow_mem (hB 0) _) (H.pow_mem (hB 1) _)) (H.pow_mem (hB 2) _))
      (H.pow_mem (hB 3) _)) (H.pow_mem (hB 4) _)) (H.pow_mem (hB 5) _)

theorem row10_range : row10OriginalMap.range = DegreeTwoZeroSixteenInterfaces.row10.top := by
  apply le_antisymm ?_ row10_top_le_range
  apply range_le_of_kernel_lifts row10Projection row10OriginalMap
    DegreeTwoZeroSixteenInterfaces.row10.top
    (row10Lifts 0) (row10Lifts 1) (row10Lifts 2) rfl rfl rfl
  · rw [row10_lifts_original]
    exact Subgroup.subset_closure (Set.mem_range_self 0)
  · rw [row10_lifts_original]
    exact Subgroup.subset_closure (Set.mem_range_self 1)
  · rw [row10_lifts_original]
    exact Subgroup.subset_closure (Set.mem_range_self 2)
  · intro g hg
    obtain ⟨x, hx, he⟩ := row10_kernel_original g hg
    rw [he]
    exact row10_translation_mem x hx

theorem row12_range : row12OriginalMap.range = DegreeTwoZeroSixteenInterfaces.row12.top := by
  apply le_antisymm ?_ row12_top_le_range
  apply range_le_of_kernel_lifts row12Projection row12OriginalMap
    DegreeTwoZeroSixteenInterfaces.row12.top
    (row12Lifts 0) (row12Lifts 1) (row12Lifts 2) rfl rfl rfl
  · rw [row12_lifts_original]
    exact Subgroup.subset_closure (Set.mem_range_self 0)
  · rw [row12_lifts_original]
    exact Subgroup.subset_closure (Set.mem_range_self 1)
  · rw [row12_lifts_original]
    exact Subgroup.subset_closure (Set.mem_range_self 2)
  · intro g hg
    obtain ⟨x, he⟩ := row12_kernel_original g hg
    rw [he]
    exact row12_translation_mem x

def row10Map : Row10Model →* DegreeTwoZeroSixteenInterfaces.row10.top :=
  row10OriginalMap.codRestrict _ (fun g => by
    rw [← row10_range]
    exact ⟨g, rfl⟩)

def row12Map : Row12Model →* DegreeTwoZeroSixteenInterfaces.row12.top :=
  row12OriginalMap.codRestrict _ (fun g => by
    rw [← row12_range]
    exact ⟨g, rfl⟩)

theorem row10Map_surjective : Function.Surjective row10Map := by
  intro y
  have hy : (y : Equiv.Perm (Fin 16)) ∈ row10OriginalMap.range := by
    rw [row10_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem row12Map_surjective : Function.Surjective row12Map := by
  intro y
  have hy : (y : Equiv.Perm (Fin 16)) ∈ row12OriginalMap.range := by
    rw [row12_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

end PrimitiveAffineDegreeTwoZeroSixteenRows10To13BlockLifts
end SymmetricSubgroupAsymptotics

end
