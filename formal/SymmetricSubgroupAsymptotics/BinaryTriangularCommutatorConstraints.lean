import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.CharP.Two

/-! A small triangular system over F2. This module proves only the
literal polynomial elimination. Binding these polynomials to entries of
an actual group representation is a separate obligation. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryTriangularCommutatorConstraints

abbrev Bits := Fin 12 → ZMod 2

def equations (b : Bits) : Fin 9 → ZMod 2 :=
  ![b 0 + b 1 + b 0*b 1,
    b 2 + b 0*b 3 + b 0*b 6 + b 1*b 6,
    b 3 + b 0*b 5 + b 2*b 6 + b 1*b 8 + b 0*b 9 + b 1*b 9 + b 0*b 1*b 9 + b 2*b 9 + b 1*b 6*b 9 + b 0*b 10 + b 1*b 10 + b 0*b 1*b 10 + b 0*b 2*b 11 + b 1*b 3*b 11 + b 0*b 6*b 11 + b 1*b 6*b 11 + b 0*b 1*b 6*b 11,
    b 3 + b 4 + b 2*b 6 + b 0*b 3*b 6 + b 0*b 9 + b 1*b 9 + b 0*b 1*b 9 + b 2*b 9 + b 1*b 6*b 9 + b 0*b 10 + b 1*b 10 + b 0*b 1*b 10,
    b 2 + b 4 + b 5 + b 6 + b 2*b 6 + b 0*b 3*b 6 + b 9 + b 0*b 1*b 9 + b 3*b 9 + b 0*b 6*b 9 + b 1*b 6*b 9 + b 10 + b 0*b 1*b 10 + b 11 + b 2*b 11,
    b 3 + b 6 + b 0*b 9 + b 0*b 11 + b 1*b 11,
    b 8 + b 9 + b 0*b 9 + b 6*b 9 + b 10 + b 0*b 10 + b 3*b 11 + b 6*b 11 + b 0*b 6*b 11,
    b 3 + b 0*b 5 + b 2*b 6 + b 3*b 6 + b 0*b 8 + b 1*b 8 + b 9 + b 0*b 1*b 9 + b 0*b 6*b 9 + b 1*b 6*b 9 + b 0*b 1*b 10 + b 2*b 11 + b 0*b 2*b 11 + b 3*b 11 + b 0*b 3*b 11 + b 1*b 3*b 11 + b 6*b 11 + b 0*b 1*b 6*b 11,
    b 3 + b 1*b 6 + b 9 + b 11 + b 0*b 11 + b 0*b 1*b 11]

private theorem bit_values (x : ZMod 2) : x=0 ∨ x=1 := by
  have h : ∀ x : ZMod 2, x=0 ∨ x=1 := by decide +kernel
  exact h x

theorem zero_shape (b : Bits) (h : ∀ j, equations b j=0) :
    b 0=0 ∧ b 1=0 ∧ b 2=0 ∧ b 3=0 ∧ b 4=0 ∧ b 6=0 ∧
    b 9=0 ∧ b 11=0 ∧ b 5=b 10 ∧ b 8=b 10 := by
  have h01 : b 0=0 ∧ b 1=0 := by
    have hh := h 0
    change b 0+b 1+b 0*b 1=0 at hh
    rcases bit_values (b 0) with h0|h0 <;>
      rcases bit_values (b 1) with h1|h1 <;> simp_all <;> norm_num at *
    exact (by decide +kernel : (3 : ZMod 2) ≠ 0) hh
  obtain ⟨h0,h1⟩ := h01
  have h2 : b 2=0 := by simpa [equations,h0,h1] using h 1
  have h3 : b 3=0 := by simpa [equations,h0,h1,h2] using h 2
  have h4 : b 4=0 := by simpa [equations,h0,h1,h2,h3] using h 3
  have h6 : b 6=0 := by simpa [equations,h0,h1,h3] using h 5
  have h9 : b 9=0 := by simpa [equations,h0,h1,h2,h3,h6] using h 7
  have h11 : b 11=0 := by simpa [equations,h0,h1,h3,h6,h9] using h 8
  have h5 : b 5=b 10 := by
    have hh : b 5+b 10=0 := by
      simpa [equations,h0,h1,h2,h3,h4,h6,h9,h11] using h 4
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
  have h8 : b 8=b 10 := by
    have hh : b 8+b 10=0 := by
      simpa [equations,h0,h1,h3,h6,h9] using h 6
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
  exact ⟨h0,h1,h2,h3,h4,h6,h9,h11,h5,h8⟩

def Solutions := {b : Bits // ∀ j, equations b j=0}

def freeCode (b : Solutions) : ZMod 2 × ZMod 2 := (b.val 7,b.val 10)

theorem freeCode_injective : Function.Injective freeCode := by
  intro a b he
  have ha := zero_shape a.val a.property
  have hb := zero_shape b.val b.property
  have h7 := congrArg Prod.fst he
  have h10 := congrArg Prod.snd he
  change a.val 7=b.val 7 at h7
  change a.val 10=b.val 10 at h10
  apply Subtype.ext
  funext i
  fin_cases i <;> simp_all

theorem card_solutions_le_four : Nat.card Solutions ≤ 4 := by
  have hh := Nat.card_le_card_of_injective freeCode freeCode_injective
  have hc : Nat.card (ZMod 2)=2 := by simp [Nat.card_eq_fintype_card]
  simpa only [Nat.card_prod,hc,Nat.reduceMul] using hh

def centralBit (epsilon : ZMod 2) : Bits := fun i => if i=7 then epsilon else 0

theorem eq_centralBit_of_last_zero (b : Bits) (h : ∀ j, equations b j=0)
    (h10 : b 10=0) : b=centralBit (b 7) := by
  have hs := zero_shape b h
  funext i
  fin_cases i <;> simp_all [centralBit]

end SymmetricSubgroupAsymptotics.BinaryTriangularCommutatorConstraints
