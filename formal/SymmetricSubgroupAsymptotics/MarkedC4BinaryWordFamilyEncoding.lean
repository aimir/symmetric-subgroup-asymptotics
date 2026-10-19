import SymmetricSubgroupAsymptotics.MarkedC4BinaryWordOriginalRecovery
import SymmetricSubgroupAsymptotics.MarkedC4ProductEncoding

/-! The original bounded binary family is injected into ONE universal
physical word family and a b!-sized original-label alphabet. The word count
retains every literal subgroup and every C4-character weight. Its subsequent
Case-I/II enumeration remains a distinct theorem to prove. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.BinaryWordFamilyEncoding
open FiniteOrbitWordShapes FiniteBinaryWordTargets

/-- Definitionally the bounded binary family used in the physical odd
convolution, without importing that entire product dependency chain. -/
abbrev Source (C b : ℕ) := {G : Subgroup (PermutationGroup b) //
  IsPGroup 2 G ∧ OrbitCutoffFamilies.OrbitCutoff C G}

def wordCount (C b r : ℕ) : ℝ :=
  ∑ T : Target C b,(Nat.card (T.image →* Multiplicative (ZMod 4)) : ℝ)^r

def encoding (C b : ℕ) :
    ProductEncoding (Source C b) (Target C b) (Equiv.Perm (Fin b))
      (fun G => G.1) (fun T => T.image) where
  code G := (actualTarget G.1 G.2.2 G.2.1,labelCode G.1 G.2.2)
  code_injective := by
    intro G H he
    apply Subtype.ext
    exact BinaryWordOriginalRecovery.source_eq G.1 G.2.2 G.2.1
      H.1 H.2.2 H.2.1 (congrArg Prod.fst he) (congrArg Prod.snd he)
  hom_card G := (hom_card_eq G.1 G.2.2 G.2.1).le

/-- Exact original-family moment reduction. In particular the character
mark r has never been reinterpreted as an orbit or subgroup multiplicity. -/
theorem moment_le (C b r : ℕ) :
    (∑ G : Source C b,(Nat.card (G.1 →* Multiplicative (ZMod 4)) : ℝ)^r) ≤
      (b.factorial : ℝ)*wordCount C b r := by
  simpa only [FiniteOrbitWordShapes.label_alphabet_card,wordCount] using
    (encoding C b).homMoment_sum_le r

end SymmetricSubgroupAsymptotics.MarkedC4.BinaryWordFamilyEncoding
