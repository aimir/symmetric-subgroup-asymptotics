import SymmetricSubgroupAsymptotics.CFSGReeGTwoSixWordTwist
import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedModelEquivalence
import Mathlib.SetTheory.Cardinal.Finite

/-! Explicit three-parameter fixed elements in the literal ORIGINAL Ree
fixed subgroup. Every fixed six-root word has exactly this normal form.
The chart is not presumed to be the full positive subgroup, and no assertion
that its elements lie in the derived subgroup is made here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalFixedWordChart
open CFSG.Models.Chevalley CFSGReeGTwoFieldParameters
open CFSGReeGTwoOriginalAutomorphism CFSGReeGTwoFixedCoordinateArithmetic
open CFSGGTwoPositiveSixWord CFSGReeGTwoSixWordTwist
open CFSGReeGTwoFixedModelEquivalence

/-- A genuine element of the fixed subgroup inside the SAME original Model. -/
def fixedWord (m : ℕ) (y : Fin 3 → Field m) : originalModelFixed m :=
  ⟨modelWord (Field m) (normalForm (alphaEquiv m) (y 0) (y 1) (y 2)),
    normalForm_modelWord_fixed m (y 0) (y 1) (y 2)⟩

theorem fixedWord_injective (m : ℕ) : Function.Injective (fixedWord m) := by
  intro y z h
  have he := congrArg (fun g : originalModelFixed m => g.val) h
  have hc : normalForm (alphaEquiv m) (y 0) (y 1) (y 2) =
      normalForm (alphaEquiv m) (z 0) (z 1) (z 2) :=
    modelWord_injective (Field m) he
  have h0 : y 0=z 0 := congrFun hc 0
  have h1 : y 1=z 1 := congrFun hc 2
  have h2 : y 2=z 2 := congrFun hc 3
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- No fixed-point lifting is used: the actual fixed word itself supplies
its three free coordinates. -/
theorem fixedWord_covers_words (m : ℕ) (g : originalModelFixed m)
    (hg : ∃ x, modelWord (Field m) x=g.val) : ∃ y, fixedWord m y=g := by
  obtain ⟨x,hx⟩ := hg
  have hfixed : reeAutomorphism m (modelWord (Field m) x)=modelWord (Field m) x := by
    rw [hx]
    exact g.property
  have hnormal : x=normalForm (alphaEquiv m) (x 0) (x 2) (x 3) :=
    (fixed_iff_normalForm _ (alpha_twice m) x).mp ((modelWord_fixed_iff m x).mp hfixed)
  refine ⟨![x 0,x 2,x 3], ?_⟩
  apply Subtype.ext
  change modelWord (Field m) (normalForm (alphaEquiv m) (x 0) (x 2) (x 3))=g.val
  exact (congrArg (modelWord (Field m)) hnormal).symm.trans hx

theorem fixedWord_range_card (m : ℕ) :
    Nat.card (Set.range (fixedWord m))=(3^(2*m+1))^3 := by
  rw [Nat.card_range_of_injective (fixedWord_injective m), Nat.card_fun,
    Nat.card_fin, field_card]

/-- Transport of the actual source words into the exact fixed subgroup in
Chevalley.Twisted, before taking any derived subgroup or central quotient. -/
def originalFixedWord (m : ℕ) (y : Fin 3 → Field m) :
    fixedSubgroup CartanMatrix.G₂ (Field m) CFSG.Models.reverseNode (originalExponent m) :=
  (originalFixedEquiv m).symm (fixedWord m y)

theorem originalFixedWord_injective (m : ℕ) :
    Function.Injective (originalFixedWord m) :=
  (originalFixedEquiv m).symm.injective.comp (fixedWord_injective m)

theorem originalFixedWord_range_card (m : ℕ) :
    Nat.card (Set.range (originalFixedWord m))=(3^(2*m+1))^3 := by
  rw [Nat.card_range_of_injective (originalFixedWord_injective m), Nat.card_fun,
    Nat.card_fin, field_card]

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalFixedWordChart
