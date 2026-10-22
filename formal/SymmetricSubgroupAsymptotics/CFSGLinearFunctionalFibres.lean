import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin

/-! Literal affine fibres of a nonzero finite-field linear functional.
An explicit vector of functional value one supplies both the splitting
and the uniform fibre count; no rank or counting premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGLinearFunctionalFibres
variable {K I : Type} [Field K] [Fintype I]

 def splitEquiv (L : (I → K) →ₗ[K] K) (w : I → K) (hw : L w = 1) :
    (I → K) ≃ K × L.ker where
  toFun x := ⟨L x, ⟨x - L x • w, by simp [map_sub, map_smul, hw]⟩⟩
  invFun p := p.2.val + p.1 • w
  left_inv x := by dsimp; abel
  right_inv p := by
    rcases p with ⟨a, k, hk⟩
    have hk' : L k = 0 := hk
    apply Prod.ext
    · simp [map_add, map_smul, hk', hw]
    · apply Subtype.ext
      simp [map_add, map_smul, hk', hw]

 def fibreEquivKer (L : (I → K) →ₗ[K] K) (w : I → K) (hw : L w = 1) (a : K) :
    {x : I → K // L x = a} ≃ L.ker where
  toFun x := ⟨x.val - a • w, by simp [map_sub, map_smul, x.property, hw]⟩
  invFun k := ⟨k.val + a • w, by simp [map_add, map_smul, hw]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv k := by apply Subtype.ext; simp

 theorem card_fibre [Finite K] (L : (I → K) →ₗ[K] K) (w : I → K)
    (hw : L w = 1) (a : K) :
    Nat.card {x : I → K // L x = a} = Nat.card K ^ (Fintype.card I - 1) := by
  have hI : 0 < Fintype.card I := by
    by_contra h
    letI : IsEmpty I := Fintype.card_eq_zero_iff.mp (by omega)
    have hzero : w = 0 := by
      funext i
      exact isEmptyElim i
    have hz : (0 : K) = 1 := by simpa only [hzero, map_zero] using hw
    exact zero_ne_one hz
  have hsplit : Nat.card K ^ Fintype.card I = Nat.card K * Nat.card L.ker := by
    have h := Nat.card_congr (splitEquiv L w hw)
    simpa only [Nat.card_fun, Nat.card_eq_fintype_card (α := I), Nat.card_prod] using h
  have hpow : Nat.card K ^ Fintype.card I =
      Nat.card K * Nat.card K ^ (Fintype.card I - 1) := by
    conv_lhs => rw [show Fintype.card I = (Fintype.card I - 1) + 1 by omega]
    rw [pow_succ, Nat.mul_comm]
  have hq : 0 < Nat.card K := Nat.card_pos
  have hker : Nat.card L.ker = Nat.card K ^ (Fintype.card I - 1) :=
    Nat.eq_of_mul_eq_mul_left hq (hsplit.symm.trans hpow)
  exact (Nat.card_congr (fibreEquivKer L w hw a)).trans hker

end SymmetricSubgroupAsymptotics.CFSGLinearFunctionalFibres
