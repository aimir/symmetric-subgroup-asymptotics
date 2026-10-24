import SymmetricSubgroupAsymptotics.CFSGSymplecticBinarySiegelStabilizerIndex
import SymmetricSubgroupAsymptotics.BinarySymmetricSquareSharpAnnihilatorIndex

/-! The stronger projective-level orbit estimate is carried through
the SAME actual Siegel stabilizer. It gives a uniform scaled index bound,
and q² from q>=4, without an assumed parabolic or coordinate stabilizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinarySiegelSharpIndex

open BinarySymmetricSquareAction CFSGSymplecticRankTwoSiegelEmbedding
open CFSGSymplecticRankTwoSiegelExtension CFSGSymplecticBinarySiegelStabilizerIndex
variable (K : Type) [Field K] [CharP K 2]

local instance sharpSiegelBaseAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- Both factors arise from the actual subgroup M; the kernel is only
viewed as a genuine prime-field subspace. -/
theorem field_mul_square_sub_one_le_two_mul_index [Finite K]
    (M : Subgroup (Siegel K)) (t : K)
    (ht : SemidirectProduct.inl (Multiplicative.ofAdd (offDiagonal K t)) ∉ M) :
    Nat.card K * (Nat.card K - 1) ^ 2 ≤ 2 * M.index := by
  let J := kernelSubmodule K M
  let L := M.map SemidirectProduct.rightHom
  have hJ : ∀ A ∈ L, ∀ S ∈ J, congruenceLinearMap A S ∈ J := by
    intro A hA S hS
    change Multiplicative.ofAdd S ∈ M.comap SemidirectProduct.inl at hS
    change congruenceAction K A (Multiplicative.ofAdd S) ∈
      M.comap SemidirectProduct.inl
    exact AbelianSemidirectStabilizerIndex.action_mem_kernel_of_projected
      (congruenceAction K) M A hA (Multiplicative.ofAdd S) hS
  have hnot : coordinates (Pi.single (1 : Fin 3) t) ∉ J := ht
  have hbound := BinarySymmetricSquareSharpAnnihilatorIndex.field_mul_square_sub_one_le_two_mul_quotient_index
    (F := ZMod 2) L J hJ t hnot
  have hc : Nat.card (Space (K := K) ⧸ J) = (M.comap SemidirectProduct.inl).index :=
    quotient_card_eq_kernel_index K M
  rw [hc] at hbound
  exact hbound.trans_eq (congrArg (fun n : ℕ => 2 * n)
    (AbelianSemidirectStabilizerIndex.index_factor (congruenceAction K) M).symm)

theorem field_square_le_index [Finite K] (hq : 4 ≤ Nat.card K)
    (M : Subgroup (Siegel K)) (t : K)
    (ht : SemidirectProduct.inl (Multiplicative.ofAdd (offDiagonal K t)) ∉ M) :
    Nat.card K ^ 2 ≤ M.index := by
  have hq3 : 3 ≤ Nat.card K - 1 := by omega
  have hm := Nat.mul_le_mul_right (Nat.card K - 1) hq3
  rw [← pow_two] at hm
  have hsquare : 2 * Nat.card K ≤ (Nat.card K - 1) ^ 2 := by omega
  have hlow : 2 * Nat.card K ^ 2 ≤ 2 * M.index := by
    calc
      _ = Nat.card K * (2 * Nat.card K) := by ring
      _ ≤ Nat.card K * (Nat.card K - 1) ^ 2 := Nat.mul_le_mul_left _ hsquare
      _ ≤ _ := field_mul_square_sub_one_le_two_mul_index K M t ht
  exact Nat.le_of_mul_le_mul_left hlow (by decide : 0 < 2)

/-- This is the actual point stabilizer of the given action. -/
theorem degree_bound_of_offDiagonal_motion [Finite K]
    {X : Type*} [Finite X] [MulAction (Siegel K) X]
    (x : X) (t : K)
    (hx : (SemidirectProduct.inl (Multiplicative.ofAdd (offDiagonal K t)) : Siegel K) • x ≠ x) :
    Nat.card K * (Nat.card K - 1) ^ 2 ≤ 2 * Nat.card X := by
  let M := MulAction.stabilizer (Siegel K) x
  have ht : (SemidirectProduct.inl (Multiplicative.ofAdd (offDiagonal K t)) : Siegel K) ∉ M := hx
  have hb := field_mul_square_sub_one_le_two_mul_index K M t ht
  have ho : M.index = Nat.card (MulAction.orbit (Siegel K) x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (Siegel K) x)).symm
  rw [ho] at hb
  exact hb.trans (Nat.mul_le_mul_left 2 (Nat.card_le_card_of_injective
    (fun y : MulAction.orbit (Siegel K) x => y.val) Subtype.val_injective))

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinarySiegelSharpIndex
