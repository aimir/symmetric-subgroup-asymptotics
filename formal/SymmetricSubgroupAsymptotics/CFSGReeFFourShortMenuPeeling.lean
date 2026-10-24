import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourShortPairedWeylMenu

/-! Residuals attached to the actual sixteen short original words.
Literal source inverses and the proved prefix factorization supply the
weighted-cover inputs; no equality with a larger prefix intersection is
asserted or needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourShortMenuPeeling
open CFSGOpposedSubgroupPeelingChain CFSGReeFFourInversionPeelingWords
open CFSGReeFFourFixedPositiveCardinality CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedModelEquivalence

def shortHead (i : Fin 16) : Bool := decide (i.val%2=0)

theorem shortWord_eq_alternating (i : Fin 16) :
    shortWord i=alternatingWord (shortHead i) (shortLength i) := by
  fin_cases i <;> rfl

theorem prefixWeight_short_eq (i : Fin 16) :
    prefixWeight (shortHead i) (shortLength i)=inversionWeight i := by
  fin_cases i <;> decide +kernel

def shortResidual (m : ℕ) (i : Fin 16) : Subgroup (originalModelFixed m) :=
  residual (fixedPositive m) (step m (shortHead i)) (shortLength i)

theorem short_prefix_eq_inverse (m : ℕ) (i : Fin 16) :
    wordPrefix (step m (shortHead i)) (shortLength i)=(shortModelWord m i)⁻¹ := by
  rw [wordPrefix_eq_inverse,←shortWord_eq_alternating]
  rfl

theorem shortResidual_le (m : ℕ) (i : Fin 16) :
    shortResidual m i≤fixedPositive m := residual_le _ _ _

theorem shortResidual_le_conjugate (m : ℕ) (i : Fin 16) :
    shortResidual m i≤(fixedPositive m).map
      (MulAut.conj ((shortModelWord m i)⁻¹)).toMonoidHom := by
  have h := residual_le_prefix (fixedPositive m) (step m (shortHead i)) (shortLength i)
  rw [short_prefix_eq_inverse] at h
  exact h

theorem shortResidual_card_factorization (m : ℕ) (i : Fin 16) :
    Nat.card (fixedPositive m)=Nat.card (shortResidual m i)*
      (2^(2*m+1))^(inversionWeight i) := by
  have hn : shortLength i≤8 := by
    simpa only [shortWord,List.length_map,List.length_range] using shortWord_length_le i
  have h := fixedPositive_card_factorization m (shortHead i) (shortLength i) hn
  rw [prefixWeight_short_eq] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGReeFFourShortMenuPeeling
