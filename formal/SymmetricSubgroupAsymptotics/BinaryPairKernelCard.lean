import SymmetricSubgroupAsymptotics.BinaryPairCoordinateSubgroups
import Mathlib.GroupTheory.Index

/-! Original source order and actual top order identify the complete
correlated kernel space after its proposed basis is proved to occur on
the same original points. No source-row enumeration or independent flip
product replaces the original action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w d : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem kernelSpace_card_mul_top :
    Nat.card F.kernelSpace*Nat.card F.top.range=Nat.card U := by
  have hk : Nat.card F.top.ker=Nat.card F.kernelSpace :=
    (Nat.card_congr F.kernelChart.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
  have h := F.top.ker.card_mul_index
  rwa [Subgroup.index_ker,hk] at h

/-- A checked correlated basis exhausts the original kernel once the
original source/top cardinal ratio is checked. -/
theorem kernelSpace_eq_of_basis_and_card (C : BinaryCoordinateSpace w d)
    (hbasis : ∀ i, C.inclusion (Pi.single i 1)∈F.kernelSpace)
    (hcard : Nat.card U=2^d*Nat.card F.top.range) : F.kernelSpace=C.space := by
  have hle := C.le_of_basis_mem F.kernelSpace hbasis
  have hp : Nat.card F.kernelSpace*Nat.card F.top.range=2^d*Nat.card F.top.range :=
    F.kernelSpace_card_mul_top.trans hcard
  have hk : Nat.card F.kernelSpace=2^d :=
    mul_right_cancel₀ (Nat.card_pos (α := F.top.range)).ne' hp
  have hc : Nat.card F.kernelSpace=2^Module.finrank (ZMod 2) F.kernelSpace := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace))
  have hpow : 2^Module.finrank (ZMod 2) F.kernelSpace=2^d := hc.symm.trans hk
  have hd := Nat.pow_right_injective (by decide : 1<2) hpow
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [C.finrank,hd]

end SymmetricSubgroupAsymptotics.BinaryPairFrame
