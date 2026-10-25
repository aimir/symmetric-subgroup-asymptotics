import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedRootWords

/-! The already proved eight-block cover has exactly twelve Boolean
parameters. Only scalar two-value and four-value encodings are checked here; this
is actual original-group coverage and uses no matrix faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedBooleanParameters
open CFSGReeFFourBinaryPositiveOrderedParameters CFSGReeFFourBinaryOrderedRootWords
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourInversionPeelingWords
open CFSGOpposedPeelingOrderedParameters CFSGFFourNormPrimeFieldWords

private def lowBit (n : ℕ) : Bool := decide (n%2=1)
private def highBit (n : ℕ) : Bool := decide (2≤n)

private theorem four_encoding (a : Fin 4) :
    (lowBit a.val).toNat+2*(highBit a.val).toNat=a.val := by
  fin_cases a <;> decide +kernel

private theorem two_encoding (a : Fin 2) : (lowBit a.val).toNat=a.val := by
  fin_cases a <;> decide +kernel

def parameterBits (a : ∀j : Fin 8,Fin (blockPeriod j)) : Fin 12 → Bool :=
  ![lowBit (a 0).val,highBit (a 0).val,lowBit (a 1).val,
    lowBit (a 2).val,highBit (a 2).val,lowBit (a 3).val,
    lowBit (a 4).val,highBit (a 4).val,lowBit (a 5).val,
    lowBit (a 6).val,highBit (a 6).val,lowBit (a 7).val]

def parameterExponents (b : Fin 12 → Bool) : Fin 8 → ℕ :=
  ![(b 0).toNat+2*(b 1).toNat,(b 2).toNat,
    (b 3).toNat+2*(b 4).toNat,(b 5).toNat,
    (b 6).toNat+2*(b 7).toNat,(b 8).toNat,
    (b 9).toNat+2*(b 10).toNat,(b 11).toNat]

theorem parameterExponents_bits (a : ∀j : Fin 8,Fin (blockPeriod j))
    (j : Fin 8) : parameterExponents (parameterBits a) j=(a j).val := by
  fin_cases j
  · exact four_encoding (a 0)
  · exact two_encoding (a 1)
  · exact four_encoding (a 2)
  · exact two_encoding (a 3)
  · exact four_encoding (a 4)
  · exact two_encoding (a 5)
  · exact four_encoding (a 6)
  · exact two_encoding (a 7)

def exponentFunction (b : Fin 12 → Bool) (n : ℕ) : ℕ :=
  if hn : n<8 then parameterExponents b ⟨n,hn⟩ else 0

theorem exponentFunction_bits (a : ∀j : Fin 8,Fin (blockPeriod j))
    (j : Fin 8) : exponentFunction (parameterBits a) j.val=(a j).val := by
  simp only [exponentFunction,dif_pos j.isLt,Fin.eta]
  exact parameterExponents_bits a j

theorem encoded_word_value (a : ∀j : Fin 8,Fin (blockPeriod j)) :
    wordValue (Field 0) (orderedLetters (exponentFunction (parameterBits a)) 8)=
      (orderedProduct (step 0 true) 8 (fun j => (blockBase j)^(a j).val)).val := by
  have hw := ordered_letters_value 0 (exponentFunction (parameterBits a)) 8
  have hf : (fun j : Fin 8 => (baseElement 0 j.val)^
      (exponentFunction (parameterBits a) j.val))=
      (fun j : Fin 8 => (blockBase j)^(a j).val) := by
    funext j
    rw [baseElement_eq_blockBase,exponentFunction_bits]
  rw [hf] at hw
  exact hw

theorem exists_encoded_positive (u : originalModelFixed 0)
    (hu : u∈fixedPositive 0) :
    ∃b : Fin 12 → Bool,
      wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val := by
  obtain ⟨a,ha⟩ := binary_power_cover u hu
  exact ⟨parameterBits a,(encoded_word_value a).trans
    (congrArg (fun g : originalModelFixed 0 => g.val) ha.symm)⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedBooleanParameters
