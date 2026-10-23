import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarRankOneAction
import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoConeGeneration

/-! Rank-one elements generate the actual natural shear group. The
proof pulls back an arbitrary subgroup to literal Hermitian coefficients
and uses the proved additive cone generation, retaining every original
root word and the same natural fixed group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUpperUnipotent

def starHermitianParameterHom (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1)) :
    Multiplicative (CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) →*
      naturalFixed (s + 3) q where
  toFun A := starFixed q s ((starHermitianEquiv q s t ht htc).symm A.toAdd)
  map_one' := by
    change starFixed q s ((starHermitianEquiv q s t ht htc).symm 0) = 1
    rw [map_zero, starFixed_zero]
  map_mul' A B := by
    change starFixed q s ((starHermitianEquiv q s t ht htc).symm (A.toAdd + B.toAdd)) = _
    rw [map_add, starFixed_add]

theorem naturalRootStarGroup_le_of_rankOne (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (H : Subgroup (naturalFixed (s + 3) q))
    (hH : ∀ (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a)
      (v : Fin 2 → q.Extension 2), starFixed q s (starRankOneParameters q s t htc a ha v) ∈ H) :
    naturalRootStarGroup q s ≤ H := by
  let phi := starHermitianParameterHom q s t ht htc
  let P : AddSubgroup (CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) :=
    { carrier := {A | phi (Multiplicative.ofAdd A) ∈ H}
      zero_mem' := by
        change phi 1 ∈ H
        rw [map_one]
        exact H.one_mem
      add_mem' := by
        intro A B hA hB
        change phi (Multiplicative.ofAdd A * Multiplicative.ofAdd B) ∈ H
        rw [map_mul]
        exact H.mul_mem hA hB
      neg_mem' := by
        intro A hA
        change phi (Multiplicative.ofAdd A)⁻¹ ∈ H
        rw [map_inv]
        exact H.inv_mem hA }
  have hP : P = ⊤ := CFSGHermitianTwoByTwoRankOne.eq_top_of_rankOne_parameters
    (definingFieldAutomorphism q 2) (fun x => extension_two_pow_twice q x) P
    (fun a ha v => hH a ha v)
  rintro g ⟨x, rfl⟩
  have hmem : (starHermitianEquiv q s t ht htc) x.toAdd ∈ P := by rw [hP]; trivial
  change starFixed q s ((starHermitianEquiv q s t ht htc).symm
    ((starHermitianEquiv q s t ht htc) x.toAdd)) ∈ H at hmem
  simpa only [AddEquiv.symm_apply_apply] using hmem

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
