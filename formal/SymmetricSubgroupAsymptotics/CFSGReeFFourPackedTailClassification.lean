import SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailSixteenPilot
import Mathlib.Tactic.FinCases

/-! The complete ten-bit classification, checked in thirty-two fixed
chunks of thirty-two masks.  Each chunk uses kernel reduction of the
same compact predicate whose prescribed sixteen-mask pilot passed.
There is no enumeration of group elements or automorphisms. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailClassification
open CFSGReeFFourPackedTailSixteenPilot

private def blockCode (b i : Fin 32) : Fin 1024 :=
  ⟨32*b.val+i.val, by omega⟩

private theorem chunk00 : ∀i : Fin 32,
    packedAdmissible (blockCode 0 i)=
      decide ((blockCode 0 i).val=64∨(blockCode 0 i).val=512∨
        (blockCode 0 i).val=864) := by
  decide +kernel

private theorem chunk01 : ∀i : Fin 32,
    packedAdmissible (blockCode 1 i)=
      decide ((blockCode 1 i).val=64∨(blockCode 1 i).val=512∨
        (blockCode 1 i).val=864) := by
  decide +kernel

private theorem chunk02 : ∀i : Fin 32,
    packedAdmissible (blockCode 2 i)=
      decide ((blockCode 2 i).val=64∨(blockCode 2 i).val=512∨
        (blockCode 2 i).val=864) := by
  decide +kernel

private theorem chunk03 : ∀i : Fin 32,
    packedAdmissible (blockCode 3 i)=
      decide ((blockCode 3 i).val=64∨(blockCode 3 i).val=512∨
        (blockCode 3 i).val=864) := by
  decide +kernel

private theorem chunk04 : ∀i : Fin 32,
    packedAdmissible (blockCode 4 i)=
      decide ((blockCode 4 i).val=64∨(blockCode 4 i).val=512∨
        (blockCode 4 i).val=864) := by
  decide +kernel

private theorem chunk05 : ∀i : Fin 32,
    packedAdmissible (blockCode 5 i)=
      decide ((blockCode 5 i).val=64∨(blockCode 5 i).val=512∨
        (blockCode 5 i).val=864) := by
  decide +kernel

private theorem chunk06 : ∀i : Fin 32,
    packedAdmissible (blockCode 6 i)=
      decide ((blockCode 6 i).val=64∨(blockCode 6 i).val=512∨
        (blockCode 6 i).val=864) := by
  decide +kernel

private theorem chunk07 : ∀i : Fin 32,
    packedAdmissible (blockCode 7 i)=
      decide ((blockCode 7 i).val=64∨(blockCode 7 i).val=512∨
        (blockCode 7 i).val=864) := by
  decide +kernel

private theorem chunk08 : ∀i : Fin 32,
    packedAdmissible (blockCode 8 i)=
      decide ((blockCode 8 i).val=64∨(blockCode 8 i).val=512∨
        (blockCode 8 i).val=864) := by
  decide +kernel

private theorem chunk09 : ∀i : Fin 32,
    packedAdmissible (blockCode 9 i)=
      decide ((blockCode 9 i).val=64∨(blockCode 9 i).val=512∨
        (blockCode 9 i).val=864) := by
  decide +kernel

private theorem chunk10 : ∀i : Fin 32,
    packedAdmissible (blockCode 10 i)=
      decide ((blockCode 10 i).val=64∨(blockCode 10 i).val=512∨
        (blockCode 10 i).val=864) := by
  decide +kernel

private theorem chunk11 : ∀i : Fin 32,
    packedAdmissible (blockCode 11 i)=
      decide ((blockCode 11 i).val=64∨(blockCode 11 i).val=512∨
        (blockCode 11 i).val=864) := by
  decide +kernel

private theorem chunk12 : ∀i : Fin 32,
    packedAdmissible (blockCode 12 i)=
      decide ((blockCode 12 i).val=64∨(blockCode 12 i).val=512∨
        (blockCode 12 i).val=864) := by
  decide +kernel

private theorem chunk13 : ∀i : Fin 32,
    packedAdmissible (blockCode 13 i)=
      decide ((blockCode 13 i).val=64∨(blockCode 13 i).val=512∨
        (blockCode 13 i).val=864) := by
  decide +kernel

private theorem chunk14 : ∀i : Fin 32,
    packedAdmissible (blockCode 14 i)=
      decide ((blockCode 14 i).val=64∨(blockCode 14 i).val=512∨
        (blockCode 14 i).val=864) := by
  decide +kernel

private theorem chunk15 : ∀i : Fin 32,
    packedAdmissible (blockCode 15 i)=
      decide ((blockCode 15 i).val=64∨(blockCode 15 i).val=512∨
        (blockCode 15 i).val=864) := by
  decide +kernel

private theorem chunk16 : ∀i : Fin 32,
    packedAdmissible (blockCode 16 i)=
      decide ((blockCode 16 i).val=64∨(blockCode 16 i).val=512∨
        (blockCode 16 i).val=864) := by
  decide +kernel

private theorem chunk17 : ∀i : Fin 32,
    packedAdmissible (blockCode 17 i)=
      decide ((blockCode 17 i).val=64∨(blockCode 17 i).val=512∨
        (blockCode 17 i).val=864) := by
  decide +kernel

private theorem chunk18 : ∀i : Fin 32,
    packedAdmissible (blockCode 18 i)=
      decide ((blockCode 18 i).val=64∨(blockCode 18 i).val=512∨
        (blockCode 18 i).val=864) := by
  decide +kernel

private theorem chunk19 : ∀i : Fin 32,
    packedAdmissible (blockCode 19 i)=
      decide ((blockCode 19 i).val=64∨(blockCode 19 i).val=512∨
        (blockCode 19 i).val=864) := by
  decide +kernel

private theorem chunk20 : ∀i : Fin 32,
    packedAdmissible (blockCode 20 i)=
      decide ((blockCode 20 i).val=64∨(blockCode 20 i).val=512∨
        (blockCode 20 i).val=864) := by
  decide +kernel

private theorem chunk21 : ∀i : Fin 32,
    packedAdmissible (blockCode 21 i)=
      decide ((blockCode 21 i).val=64∨(blockCode 21 i).val=512∨
        (blockCode 21 i).val=864) := by
  decide +kernel

private theorem chunk22 : ∀i : Fin 32,
    packedAdmissible (blockCode 22 i)=
      decide ((blockCode 22 i).val=64∨(blockCode 22 i).val=512∨
        (blockCode 22 i).val=864) := by
  decide +kernel

private theorem chunk23 : ∀i : Fin 32,
    packedAdmissible (blockCode 23 i)=
      decide ((blockCode 23 i).val=64∨(blockCode 23 i).val=512∨
        (blockCode 23 i).val=864) := by
  decide +kernel

private theorem chunk24 : ∀i : Fin 32,
    packedAdmissible (blockCode 24 i)=
      decide ((blockCode 24 i).val=64∨(blockCode 24 i).val=512∨
        (blockCode 24 i).val=864) := by
  decide +kernel

private theorem chunk25 : ∀i : Fin 32,
    packedAdmissible (blockCode 25 i)=
      decide ((blockCode 25 i).val=64∨(blockCode 25 i).val=512∨
        (blockCode 25 i).val=864) := by
  decide +kernel

private theorem chunk26 : ∀i : Fin 32,
    packedAdmissible (blockCode 26 i)=
      decide ((blockCode 26 i).val=64∨(blockCode 26 i).val=512∨
        (blockCode 26 i).val=864) := by
  decide +kernel

private theorem chunk27 : ∀i : Fin 32,
    packedAdmissible (blockCode 27 i)=
      decide ((blockCode 27 i).val=64∨(blockCode 27 i).val=512∨
        (blockCode 27 i).val=864) := by
  decide +kernel

private theorem chunk28 : ∀i : Fin 32,
    packedAdmissible (blockCode 28 i)=
      decide ((blockCode 28 i).val=64∨(blockCode 28 i).val=512∨
        (blockCode 28 i).val=864) := by
  decide +kernel

private theorem chunk29 : ∀i : Fin 32,
    packedAdmissible (blockCode 29 i)=
      decide ((blockCode 29 i).val=64∨(blockCode 29 i).val=512∨
        (blockCode 29 i).val=864) := by
  decide +kernel

private theorem chunk30 : ∀i : Fin 32,
    packedAdmissible (blockCode 30 i)=
      decide ((blockCode 30 i).val=64∨(blockCode 30 i).val=512∨
        (blockCode 30 i).val=864) := by
  decide +kernel

private theorem chunk31 : ∀i : Fin 32,
    packedAdmissible (blockCode 31 i)=
      decide ((blockCode 31 i).val=64∨(blockCode 31 i).val=512∨
        (blockCode 31 i).val=864) := by
  decide +kernel

private theorem all_blocks (b i : Fin 32) :
    packedAdmissible (blockCode b i)=
      decide ((blockCode b i).val=64∨(blockCode b i).val=512∨
        (blockCode b i).val=864) := by
  fin_cases b
  · exact chunk00 i
  · exact chunk01 i
  · exact chunk02 i
  · exact chunk03 i
  · exact chunk04 i
  · exact chunk05 i
  · exact chunk06 i
  · exact chunk07 i
  · exact chunk08 i
  · exact chunk09 i
  · exact chunk10 i
  · exact chunk11 i
  · exact chunk12 i
  · exact chunk13 i
  · exact chunk14 i
  · exact chunk15 i
  · exact chunk16 i
  · exact chunk17 i
  · exact chunk18 i
  · exact chunk19 i
  · exact chunk20 i
  · exact chunk21 i
  · exact chunk22 i
  · exact chunk23 i
  · exact chunk24 i
  · exact chunk25 i
  · exact chunk26 i
  · exact chunk27 i
  · exact chunk28 i
  · exact chunk29 i
  · exact chunk30 i
  · exact chunk31 i

theorem packedAdmissible_iff (c : Fin 1024) :
    packedAdmissible c=true ↔ c=64∨c=512∨c=864 := by
  let b : Fin 32 := ⟨c.val/32, by omega⟩
  let i : Fin 32 := ⟨c.val%32, Nat.mod_lt _ (by decide)⟩
  have hcode : blockCode b i=c := by
    apply Fin.ext
    change 32*(c.val/32)+c.val%32=c.val
    omega
  have h := all_blocks b i
  rw [hcode] at h
  rw [h]
  simp only [decide_eq_true_eq,Fin.ext_iff]
  rfl

theorem code_of_packedAdmissible (c : Fin 1024) (h : packedAdmissible c=true) :
    c=64∨c=512∨c=864 :=
  (packedAdmissible_iff c).mp h

end SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailClassification
