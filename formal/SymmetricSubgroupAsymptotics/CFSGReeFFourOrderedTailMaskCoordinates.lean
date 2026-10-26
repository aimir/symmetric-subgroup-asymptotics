import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedBooleanParameters
import Init.Data.BitVec.Lemmas
import Mathlib.Tactic.FinCases

/-! Exact low-bit coordinates for the covered ten-bit middle tail.
The first two bits of the existing twelve-bit chart are zero. Encoding
uses the core little-endian bitvector theorem rather than an exhaustive
existence search over pairs of masks. No finite root condition is imposed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOrderedTailMaskCoordinates

def tailBits (c : Fin 1024) : Fin 12→Bool :=
  ![false,false,c.val.testBit 0,c.val.testBit 1,c.val.testBit 2,c.val.testBit 3,
    c.val.testBit 4,c.val.testBit 5,c.val.testBit 6,c.val.testBit 7,
    c.val.testBit 8,c.val.testBit 9]

def tailPart (b : Fin 12→Bool) : Fin 10→Bool :=
  ![b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11]

private def bitList (t : Fin 10→Bool) : List Bool :=
  [t 0,t 1,t 2,t 3,t 4,t 5,t 6,t 7,t 8,t 9]

private theorem bitList_length (t : Fin 10→Bool) : (bitList t).length=10 := rfl

private def encodedVector (t : Fin 10→Bool) : BitVec (bitList t).length :=
  BitVec.ofBoolListLE (bitList t)

def encodeBits (t : Fin 10→Bool) : Fin 1024 :=
  Fin.cast (congrArg (fun n : ℕ=>2^n) (bitList_length t)) (encodedVector t).toFin

private theorem encodeBits_val (t : Fin 10→Bool) :
    (encodeBits t).val=(BitVec.ofBoolListLE (bitList t)).toNat := rfl

theorem encodeBits_bit (t : Fin 10→Bool) (i : Fin 10) :
    (encodeBits t).val.testBit i.val=t i := by
  rw [encodeBits_val]
  change (BitVec.ofBoolListLE (bitList t)).getLsbD i.val=t i
  rw [BitVec.getLsbD_ofBoolListLE]
  fin_cases i <;> rfl

theorem tailBits_encode (b : Fin 12→Bool) (h0 : b 0=false) (h1 : b 1=false) :
    tailBits (encodeBits (tailPart b))=b := by
  funext i
  fin_cases i
  · exact h0.symm
  · exact h1.symm
  · exact encodeBits_bit (tailPart b) 0
  · exact encodeBits_bit (tailPart b) 1
  · exact encodeBits_bit (tailPart b) 2
  · exact encodeBits_bit (tailPart b) 3
  · exact encodeBits_bit (tailPart b) 4
  · exact encodeBits_bit (tailPart b) 5
  · exact encodeBits_bit (tailPart b) 6
  · exact encodeBits_bit (tailPart b) 7
  · exact encodeBits_bit (tailPart b) 8
  · exact encodeBits_bit (tailPart b) 9

theorem exists_code (b : Fin 12→Bool) (h0 : b 0=false) (h1 : b 1=false) :
    ∃c : Fin 1024,tailBits c=b :=
  ⟨encodeBits (tailPart b),tailBits_encode b h0 h1⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourOrderedTailMaskCoordinates
