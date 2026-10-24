import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-! The nondegenerate trace pairing over the literal Frobenius-fixed
subfield of the quadratic coefficient field.  The trace-one witness
works in characteristic two as well.  Both coordinate equivalences are
over that same fixed subfield; no abstract field identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGQuadraticTracePairing
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField
open CFSGTwistedA2TraceFibers CFSGTwistedAQuadraticTrace
open Module

def traceLinear (q : CFSG.PrimePower) :
    q.Extension 2 →ₗ[fixedField q] fixedField q where
  toFun x := ⟨traceHom q x, trace_fixed q x⟩
  map_add' x y := Subtype.ext ((traceHom q).map_add x y)
  map_smul' c x := by
    apply Subtype.ext
    have hc : definingFieldAutomorphism q 2 (c : q.Extension 2) = c := c.property
    change (c : q.Extension 2) * x +
        definingFieldAutomorphism q 2 ((c : q.Extension 2) * x) =
      (c : q.Extension 2) * (x + definingFieldAutomorphism q 2 x)
    rw [map_mul, hc, mul_add]

@[simp] theorem traceLinear_val (q : CFSG.PrimePower) (x : q.Extension 2) :
    (traceLinear q x).val = x + definingFieldAutomorphism q 2 x := rfl

theorem traceLinear_surjective (q : CFSG.PrimePower) :
    Function.Surjective (traceLinear q) := by
  intro c
  obtain ⟨x, hx⟩ := exists_trace_eq_fixed q c.val c.property
  exact ⟨x, Subtype.ext hx⟩

def pairing (q : CFSG.PrimePower) :
    LinearMap.BilinForm (fixedField q) (q.Extension 2) where
  toFun x :=
    { toFun := fun y => traceLinear q (x * y)
      map_add' := fun y z => by rw [mul_add, map_add]
      map_smul' := fun c y => by
        change traceLinear q (x * ((c : q.Extension 2) * y)) = _
        rw [show x * ((c : q.Extension 2) * y) =
          (c : q.Extension 2) * (x * y) by ring]
        exact (traceLinear q).map_smul c (x * y) }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change traceLinear q ((x + y) * z) = traceLinear q (x * z) + traceLinear q (y * z)
    rw [add_mul, map_add]
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    change traceLinear q (((c : q.Extension 2) * x) * y) = _
    rw [mul_assoc]
    exact (traceLinear q).map_smul c (x * y)

@[simp] theorem pairing_apply (q : CFSG.PrimePower) (x y : q.Extension 2) :
    pairing q x y = traceLinear q (x * y) := rfl

theorem pairing_symm (q : CFSG.PrimePower) : (pairing q).IsSymm := by
  refine ⟨?_⟩
  intro x y
  change traceLinear q (x * y) = traceLinear q (y * x)
  exact congrArg (traceLinear q) (mul_comm x y)

theorem pairing_surjective_right (q : CFSG.PrimePower) (x : q.Extension 2)
    (hx : x ≠ 0) : Function.Surjective (pairing q x) := by
  intro c
  obtain ⟨u, hu⟩ := traceLinear_surjective q c
  refine ⟨u / x, ?_⟩
  rw [pairing_apply, show x * (u / x) = u by field_simp]
  exact hu

theorem pairing_nondegenerate (q : CFSG.PrimePower) :
    (pairing q).Nondegenerate := by
  have hleft : (pairing q).SeparatingLeft := by
    intro x hx
    by_contra hne
    obtain ⟨y, hy⟩ := pairing_surjective_right q x hne 1
    exact one_ne_zero (hy.symm.trans (hx y))
  refine ⟨hleft, ?_⟩
  intro y hy
  apply hleft y
  intro x
  exact ((pairing_symm q).eq y x).trans (hy x)

theorem extension_finrank (q : CFSG.PrimePower) :
    Module.finrank (fixedField q) (q.Extension 2) = 2 := by
  apply Nat.pow_right_injective (order_two_le q)
  have h := Module.natCard_eq_pow_finrank (K := fixedField q) (V := q.Extension 2)
  rw [fixedField_card, CFSGTwistedANaturalMatrices.extension_two_card] at h
  exact h.symm

def fieldBasis (q : CFSG.PrimePower) :
    Basis (Fin 2) (fixedField q) (q.Extension 2) :=
  Module.finBasisOfFinrankEq (fixedField q) (q.Extension 2) (extension_finrank q)

def firstCoordinates (q : CFSG.PrimePower) :
    (q.Extension 2) ≃ₗ[fixedField q] (Fin 2 → fixedField q) :=
  (fieldBasis q).equivFun

def secondCoordinates (q : CFSG.PrimePower) :
    (q.Extension 2) ≃ₗ[fixedField q] (Fin 2 → fixedField q) :=
  ((pairing q).dualBasis (pairing_nondegenerate q) (fieldBasis q)).equivFun

theorem pairing_eq_coordinate_sum (q : CFSG.PrimePower) (x y : q.Extension 2) :
    pairing q x y =
      ∑ i : Fin 2, firstCoordinates q x i * secondCoordinates q y i := by
  classical
  have h := congrArg (fun z => pairing q y z) ((fieldBasis q).sum_repr x)
  calc
    pairing q x y = pairing q y x := (pairing_symm q).eq x y
    _ = _ := by
      simpa only [map_sum, map_smul, smul_eq_mul, firstCoordinates, secondCoordinates,
        Basis.equivFun_apply, LinearMap.BilinForm.dualBasis_repr_apply] using h.symm

end SymmetricSubgroupAsymptotics.CFSGQuadraticTracePairing
