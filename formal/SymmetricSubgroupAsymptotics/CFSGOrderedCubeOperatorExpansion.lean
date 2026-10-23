import SymmetricSubgroupAsymptotics.CFSGCubicNormMonomialSeparation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Module

/-! Ordered three-factor linear expansion with the exact cubic norm
monomials. Operator commutation, sign coherence, and identification
with a group action are not assumptions of this expansion. The word
of binary index i is N2^bit2 N1^bit1 N0^bit0 v, in that order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrderedCubeOperatorExpansion
open CFSGCubicNormMonomialSeparation
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def tensorWord (N0 N1 N2 : V →ₗ[K] V) (v : V) (i : Fin 8) : V :=
  match i.val with
  | 0 => v
  | 1 => N0 v
  | 2 => N1 v
  | 3 => N1 (N0 v)
  | 4 => N2 v
  | 5 => N2 (N0 v)
  | 6 => N2 (N1 v)
  | _ => N2 (N1 (N0 v))

def cubeParameters (a b c : K) (i : Fin 8) : K :=
  match i.val with
  | 0 => 1
  | 1 => a
  | 2 => b
  | 3 => b*a
  | 4 => c
  | 5 => c*a
  | 6 => c*b
  | _ => c*b*a

def orderedAction (N0 N1 N2 : V →ₗ[K] V) (v : V) (a b c : K) : V :=
  ((LinearMap.id : V →ₗ[K] V) + c • N2)
    (((LinearMap.id : V →ₗ[K] V) + b • N1)
      (((LinearMap.id : V →ₗ[K] V) + a • N0) v))

theorem orderedAction_expansion (N0 N1 N2 : V →ₗ[K] V) (v : V) (a b c : K) :
    orderedAction N0 N1 N2 v a b c =
      ∑ i : Fin 8, cubeParameters a b c i • tensorWord N0 N1 N2 v i := by
  simp only [orderedAction, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smul_apply, map_add, map_smul, smul_add, smul_smul,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_succ,
    cubeParameters, tensorWord, one_smul]
  module

theorem cubeParameters_eq_normCurve (q : ℕ) (t : K) :
    cubeParameters t (t^q) (t^(q^2)) = normCurve q t := by
  funext i
  fin_cases i <;> simp [cubeParameters, normCurve, exponent, pow_add]

def tensorMap (N0 N1 N2 : V →ₗ[K] V) (v : V) : (Fin 8 → K) →ₗ[K] V :=
  Fintype.linearCombination K (tensorWord N0 N1 N2 v)

theorem orderedAction_normCurve (N0 N1 N2 : V →ₗ[K] V) (v : V) (q : ℕ) (t : K) :
    orderedAction N0 N1 N2 v t (t^q) (t^(q^2)) =
      tensorMap N0 N1 N2 v (normCurve q t) := by
  rw [orderedAction_expansion, cubeParameters_eq_normCurve]
  rfl

end SymmetricSubgroupAsymptotics.CFSGOrderedCubeOperatorExpansion
