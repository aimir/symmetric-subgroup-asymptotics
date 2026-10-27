import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYCentralizerFiniteEncoding
import Mathlib.Data.Nat.Bitwise

/-! A proof-erased point decoder for the SAME actual y-centralizer chart.
Only the twelve coordinate labels and the 24 four-point permutations are
checked finitely. The 1944-code point binding is symbolic. Witt mask bits
are a necessary condition only; collisions or false positives are harmless. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYRawPointMaskCoding
open CFSG.Certificates.Mathieu12 M12Certificates.WittDesign
open CFSGMathieuTwelveYCyclicCentralizerChart
open CFSGMathieuTwelveYCentralizerFiniteEncoding

def rawBlock : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 2 | 4 => 2 | 5 => 1
  | 6 => 3 | 7 => 0 | 8 => 3 | 9 => 3 | 10 => 0 | _ => 1

def rawPhase : ℕ → ℕ
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 2
  | 6 => 0 | 7 => 1 | 8 => 1 | 9 => 2 | 10 => 2 | _ => 1

def rawFrom (b t : ℕ) : ℕ :=
  match b,t with
  | 0,0 => 0 | 0,1 => 7 | 0,_ => 10
  | 1,0 => 1 | 1,1 => 11 | 1,_ => 5
  | 2,0 => 2 | 2,1 => 4 | 2,_ => 3
  | _,0 => 6 | _,1 => 8 | _,_ => 9

def rawBeta (i b : ℕ) : ℕ :=
  (match i with
  | 0 => [0,1,2,3] | 1 => [0,1,3,2] | 2 => [0,2,1,3]
  | 3 => [0,2,3,1] | 4 => [0,3,1,2] | 5 => [0,3,2,1]
  | 6 => [1,0,2,3] | 7 => [1,0,3,2] | 8 => [1,2,0,3]
  | 9 => [1,2,3,0] | 10 => [1,3,0,2] | 11 => [1,3,2,0]
  | 12 => [2,0,1,3] | 13 => [2,0,3,1] | 14 => [2,1,0,3]
  | 15 => [2,1,3,0] | 16 => [2,3,0,1] | 17 => [2,3,1,0]
  | 18 => [3,0,1,2] | 19 => [3,0,2,1] | 20 => [3,1,0,2]
  | 21 => [3,1,2,0] | 22 => [3,2,0,1] | _ => [3,2,1,0]).getD b 0

def rawDigit (c b : ℕ) : ℕ := ((c % 81) / 3^b) % 3

def rawPoint (c p : ℕ) : ℕ :=
  rawFrom (rawBeta (c/81) (rawBlock p))
    ((rawPhase p + rawDigit c (rawBlock p)) % 3)

theorem rawBlock_binding (p : Fin 12) : rawBlock p.val = (coordinates p).1.val := by
  fin_cases p <;> decide +kernel

theorem rawPhase_binding (p : Fin 12) : rawPhase p.val = (coordinates p).2.val := by
  fin_cases p <;> decide +kernel

theorem rawFrom_binding (b : Fin 4) (t : ZMod 3) :
    rawFrom b.val t.val = (coordinates.symm (b,t)).val := by
  fin_cases b <;> fin_cases t <;> decide +kernel

theorem rawBeta_binding (i : Fin 24) (b : Fin 4) :
    rawBeta i.val b.val = (permutation i b).val := by
  fin_cases i <;> fin_cases b <;> decide +kernel

theorem rawPoint_eq (c : Fin 1944) (p : Fin 12) :
    rawPoint c.val p.val = (indexedChart c p).val := by
  let i : Fin 24 := ⟨c.val/81,by omega⟩
  let j : Fin 81 := ⟨c.val%81,Nat.mod_lt _ (by decide)⟩
  let b := (coordinates p).1
  let t := (coordinates p).2
  have hd : rawDigit c.val b.val = (phases j b).val := by
    simp only [rawDigit,phases,ZMod.val_natCast,j]
  have hform : indexedChart c p = coordinates.symm (permutation i b,t+phases j b) := by
    apply coordinates.injective
    rw [Equiv.apply_symm_apply]
    exact chart_coordinate (decodeCode c) p
  calc
    rawPoint c.val p.val =
        rawFrom (permutation i b).val ((t.val+rawDigit c.val b.val)%3) := by
      unfold rawPoint
      rw [rawBlock_binding,rawPhase_binding]
      exact congrArg (fun z => rawFrom z ((t.val+rawDigit c.val b.val)%3))
        (rawBeta_binding i b)
    _ = rawFrom (permutation i b).val (t+phases j b).val := by
      rw [ZMod.val_add,hd]
    _ = (coordinates.symm (permutation i b,t+phases j b)).val :=
      rawFrom_binding _ _
    _ = (indexedChart c p).val := congrArg Fin.val hform.symm

def pointMap (c : Fin 1944) (p : Fin 12) : Fin 12 :=
  ⟨rawPoint c.val p.val % 12,Nat.mod_lt _ (by decide)⟩

theorem pointMap_eq (c : Fin 1944) : pointMap c = (indexedChart c : Fin 12 → Fin 12) := by
  funext p
  apply Fin.ext
  change rawPoint c.val p.val % 12 = (indexedChart c p).val
  rw [rawPoint_eq,Nat.mod_eq_of_lt (indexedChart c p).isLt]

def blockMask (B : Block) : ℕ := ∑ p ∈ B, 2^p.val

theorem witt_member_bit (bitmap : ℕ)
    (hbits : ∀ k : Fin 132, bitmap.testBit (blockMask (wittBlockAt k)) = true)
    {B : Block} (hB : B ∈ wittBlocks) : bitmap.testBit (blockMask B) = true := by
  have hall : ∀ B ∈ wittBlockList, bitmap.testBit (blockMask B) = true := by
    rw [List.forall_mem_iff_get]
    intro i
    obtain ⟨j,hget⟩ := exists_wittBlockAt_eq_get i
    rw [hget]
    exact hbits j
  exact hall B (mem_wittBlockList_of_mem_wittBlocks hB)

theorem not_mem_of_bit_false (bitmap : ℕ)
    (hbits : ∀ k : Fin 132, bitmap.testBit (blockMask (wittBlockAt k)) = true)
    (B : Block) (hfalse : bitmap.testBit (blockMask B) = false) : B ∉ wittBlocks := by
  intro hB
  have htrue := witt_member_bit bitmap hbits hB
  rw [hfalse] at htrue
  cases htrue

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYRawPointMaskCoding
