import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! Compact binary row multiplication with an exact matrix semantics.
Only the selected finite row width is decoded; no injectivity or bound
on unused high bits is needed. The arithmetic checker uses literal Nat
xor, while the theorem below identifies it with genuine ZMod2 matrix
multiplication. The sole closed pilot is two by two. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryPackedMatrix

def bit (a j : ℕ) : ZMod 2 := if a.testBit j then 1 else 0

def xorSum : List ℕ→ℕ
  | []=>0
  | a::l=>a ^^^ xorSum l

theorem bit_xor (a b j : ℕ) : bit (a ^^^ b) j=bit a j+bit b j := by
  unfold bit
  rw [Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide +kernel

theorem bit_xorSum (l : List ℕ) (j : ℕ) :
    bit (xorSum l) j=(l.map (fun a=>bit a j)).sum := by
  induction l with
  | nil=>simp only [xorSum,bit,Nat.zero_testBit,Bool.false_eq_true,if_false,
      List.map_nil,List.sum_nil]
  | cons a l ih=>simp only [xorSum,bit_xor,List.map_cons,List.sum_cons,ih]

abbrev Rows (n : ℕ) := Fin n→ℕ

def decode {n : ℕ} (A : Rows n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j=>bit (A i) j.val

def mul {n : ℕ} (A B : Rows n) : Rows n := fun i=>
  xorSum (List.ofFn (fun k : Fin n=>if (A i).testBit k.val then B k else 0))

theorem decode_mul {n : ℕ} (A B : Rows n) : decode (mul A B)=decode A*decode B := by
  ext i j
  change bit (xorSum (List.ofFn (fun k : Fin n=>
      if (A i).testBit k.val then B k else 0))) j.val=
    ∑k : Fin n,bit (A i) k.val*bit (B k) j.val
  rw [bit_xorSum,List.map_ofFn,Fin.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  cases h : (A i).testBit k.val <;> simp [bit,h]

theorem two_by_two_pilot : mul (![1,3] : Rows 2) ![3,2]=![3,1] := by
  decide +kernel

end SymmetricSubgroupAsymptotics.BinaryPackedMatrix
