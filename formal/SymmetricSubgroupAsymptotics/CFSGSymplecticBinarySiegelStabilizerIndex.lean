import SymmetricSubgroupAsymptotics.CFSGSymplecticRankTwoSiegelExtension
import SymmetricSubgroupAsymptotics.AbelianSemidirectStabilizerIndex
import SymmetricSubgroupAsymptotics.BinarySymmetricSquareAnnihilatorIndex
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Quotient.Card

/-! An actual subgroup of the literal C2 Siegel semidirect product has
index at least q² if it misses an off-diagonal parameter, in characteristic
two with q at least eight. Its additive kernel is used only as a genuine
prime-field subspace, and its projected stabilizer is derived from M. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinarySiegelStabilizerIndex

open BinarySymmetricSquareAction CFSGSymplecticRankTwoSiegelEmbedding
open CFSGSymplecticRankTwoSiegelExtension
variable (K : Type) [Field K] [CharP K 2]

local instance binarySiegelBaseAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2

abbrev Siegel := Multiplicative (Space (K := K)) ⋊[congruenceAction K]
  GeneralLinear (K := K)

/-- The actual additive kernel preimage belonging to M. -/
def kernelAdditive (M : Subgroup (Siegel K)) : AddSubgroup (Space (K := K)) where
  carrier := {S | Multiplicative.ofAdd S ∈ M.comap SemidirectProduct.inl}
  zero_mem' := (M.comap SemidirectProduct.inl).one_mem
  add_mem' := fun hS hT => (M.comap SemidirectProduct.inl).mul_mem hS hT
  neg_mem' := fun hS => (M.comap SemidirectProduct.inl).inv_mem hS

/-- Only prime-field linearity is asserted. -/
def kernelSubmodule (M : Subgroup (Siegel K)) : Submodule (ZMod 2) (Space (K := K)) :=
  AddSubgroup.toZModSubmodule 2 (kernelAdditive K M)

theorem quotient_card_eq_kernel_index [Finite K] (M : Subgroup (Siegel K)) :
    Nat.card (Space (K := K) ⧸ kernelSubmodule K M) =
      (M.comap SemidirectProduct.inl).index := by
  let J := kernelSubmodule K M
  let U := M.comap (SemidirectProduct.inl : Multiplicative (Space (K := K)) →* Siegel K)
  have hJ : Nat.card J = Nat.card U := rfl
  have hN : Nat.card (Multiplicative (Space (K := K))) = Nat.card (Space (K := K)) :=
    Nat.card_congr Multiplicative.toAdd
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := J))
  calc
    Nat.card J * Nat.card (Space (K := K) ⧸ J) = Nat.card (Space (K := K)) :=
      (Submodule.card_eq_card_quotient_mul_card J).symm
    _ = Nat.card U * U.index := hN.symm.trans U.card_mul_index.symm
    _ = Nat.card J * U.index := by rw [hJ]

/-- The two factors come from the same actual subgroup M. No separate
parabolic or prime-field stabilizer assumption is an input. -/
theorem field_square_le_index [Finite K] (hq : 8 ≤ Nat.card K)
    (M : Subgroup (Siegel K)) (t : K)
    (ht : SemidirectProduct.inl (Multiplicative.ofAdd (offDiagonal K t)) ∉ M) :
    Nat.card K ^ 2 ≤ M.index := by
  let J := kernelSubmodule K M
  let L := M.map SemidirectProduct.rightHom
  have hJ : ∀ A ∈ L, ∀ S ∈ J, congruenceLinearMap A S ∈ J := by
    intro A hA S hS
    change Multiplicative.ofAdd S ∈ M.comap SemidirectProduct.inl at hS
    change congruenceAction K A (Multiplicative.ofAdd S) ∈
      M.comap SemidirectProduct.inl
    exact AbelianSemidirectStabilizerIndex.action_mem_kernel_of_projected
      (congruenceAction K) M A hA (Multiplicative.ofAdd S) hS
  have hnot : coordinates (Pi.single (1 : Fin 3) t) ∉ J := by
    exact ht
  have hbound := BinarySymmetricSquareAnnihilatorIndex.field_square_le_quotient_card_mul_index
    (F := ZMod 2) hq L J hJ t hnot
  have hc : Nat.card (Space (K := K) ⧸ J) = (M.comap SemidirectProduct.inl).index :=
    quotient_card_eq_kernel_index K M
  rw [hc] at hbound
  exact hbound.trans_eq
    (AbelianSemidirectStabilizerIndex.index_factor (congruenceAction K) M).symm

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinarySiegelStabilizerIndex
