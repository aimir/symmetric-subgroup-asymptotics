import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareOriginalWords
import SymmetricSubgroupAsymptotics.ThreeCentralBracketProduct

/-! A literal all-parameter original fixed-group commutator expressing
a conjugate of the middle square. The proof collects selected Chevalley
parameters and returns through the faithful original map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareCommutator
open CFSGReeFFourMiddleSquareOriginalWords CFSGReeFFourMiddleSquareRootWordValues
open CFSGReeFFourMiddleSquareBracketRootRelations CFSGFFourOriginalMiddleWords
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence

private theorem fixedRaw_injective (m : ℕ) : Function.Injective (fixedRawHom m) := by
  intro a b h
  apply Subtype.ext
  apply rawHom_injective (Field m)
  exact h

theorem canonical_commutator (K : Type) [CommRing K] [CharP K 2] :
    ⁅yWord K,uWord K⁆ = squareWord K := by
  rw [yWord_eq,uWord_eq,squareWord_eq]
  apply ThreeCentralBracketProduct.collect
    (fun i => yParameter K i 1) (fun j => uParameter K j 1)
    (fun j => bracketParameter K j 1)
  · intro i j
    by_cases hij : i = j.castSucc
    · subst i
      rw [if_pos rfl]
      simpa only [one_mul] using paired_commutator K j 1 1
    · rw [if_neg hij]
      exact (cross_commute K i j hij 1 1).commutator_eq
  · exact fun i j => y_bracket_commute K i j 1 1
  · exact fun i j => u_bracket_commute K i j 1 1
  · exact fun i j => bracket_commute K i j 1 1

theorem commutator_identity (m : ℕ) :
    ⁅fourCycle m,outerConjugate m⁆ =
      (middleFixedWeyl m*outerFixedWeyl m)*(fourCycle m)^2*
        (middleFixedWeyl m*outerFixedWeyl m)⁻¹ := by
  apply fixedRaw_injective m
  rw [map_commutatorElement,raw_fourCycle,raw_outerConjugate,raw_conjugateSquare]
  exact canonical_commutator (Field m)

theorem square_mem_derived (m : ℕ) :
    (fourCycle m)^2 ∈ commutator (originalModelFixed m) := by
  let D := commutator (originalModelFixed m)
  let v := middleFixedWeyl m*outerFixedWeyl m
  have h : ⁅fourCycle m,outerConjugate m⁆ ∈ D :=
    Subgroup.commutator_mem_commutator (by trivial) (by trivial)
  rw [commutator_identity] at h
  have hc := (inferInstance : D.Normal).conj_mem' _ h v
  have he : v⁻¹*((middleFixedWeyl m*outerFixedWeyl m)*(fourCycle m)^2*
      (middleFixedWeyl m*outerFixedWeyl m)⁻¹)*v = (fourCycle m)^2 := by
    dsimp only [v]
    group
  rw [he] at hc
  exact hc

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareCommutator
