import SymmetricSubgroupAsymptotics.PrimitiveAffineFiniteDegreeSplit
import SymmetricSubgroupAsymptotics.PrimitiveAffineLargeSoConsumer
import SymmetricSubgroupAsymptotics.PrimitiveAffineOrderTailSource
import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeDegreeSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineMediumOddSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineNonsolubleSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineNonsolubleSmallSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineNonsolubleExceptionalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleOddOrderSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleSmallCentralSource
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimDegreeFive
import SymmetricSubgroupAsymptotics.Non2PreE7F20MarkedC4Source

/-!
# Exhaustive consumer for primitive affine actions

This file threads the profile-native affine source theorems through the
prime-power degree split.  The external boundary consists only of published
finite structural facts: the degree-five affine group classification,
solvability in degree nine, and the already isolated composition/order data
for the exceptional small linear groups.  No epimorphism, moment, menu-mass,
or asymptotic estimate is assumed here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Published finite structural facts needed after the generic affine
theorems have reduced the primitive problem to degrees below `343`.

The first field is the standard classification of transitive affine groups
of prime degree five: their complement has order `1`, `2`, or `4`.  The
remaining fields are the previously isolated subgroup/composition facts for
small primitive linear groups. -/
structure PublishedPrimitiveAffineFiniteInput where
  nonsolubleSmall : PublishedNonsolublePrimitiveAffineSmallCompositionInput
  solubleOdd : PublishedSolublePrimitiveAffineExceptionalOrderInput
  solubleCentral : PublishedSolublePrimitiveAffineSmallCentralInput
  degreeFive : ∀ (U : PreE7NonPairActionClass 5)
    (_P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5))
    (_hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 5 U) (Fin 5)),
      PreE7SaprimDegreeFiveSource 5 U ⊕ PLift (PreE7F20Source 5 U)
  degreeNineSolvable : ∀ (U : PreE7NonPairActionClass 9)
    (P : PrimitiveAffineProfile (preE7NonPairAction 9 U) (Fin 9))
    (x : Fin 9), IsSolvable (P.complement x)

namespace PublishedPrimitiveAffineFiniteInput

private noncomputable def degreeFiveSource
    (published : PublishedPrimitiveAffineFiniteInput)
    (U : PreE7NonPairActionClass 5)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 5 U) (Fin 5))
    (P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5)) :
    PreE7RankTailOwnerSourceData 5 U :=
  match published.degreeFive U P hprimitive with
  | .inl S => .ordinary .saprim (.small S.numericalData)
  | .inr S => .f20 S.down

/-- Every primitive affine profile supplies an already integrated numerical
owner.  All infinite families are handled by proved generic estimates; the
finite structural input is used only in the explicitly displayed small
degrees. -/
noncomputable def primitiveOwner
    (published : PublishedPrimitiveAffineFiniteInput)
    (hcomp : PrimitiveCompositionLengthInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    {w : ℕ} (U : PreE7NonPairActionClass w) (hw5 : 5 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w)) :
    PreE7RankTailOwnerSourceData w U := by
  by_cases hw1024 : 1024 ≤ w
  · exact primitiveAffineLarge_rankTailOwnerSourceData U hw1024 P
  have hw1024' : w < 1024 := by omega
  by_cases hw343 : 343 ≤ w
  · exact PrimitiveAffineOrderTailSource.toRankTailOwnerSource
      P hw343 hw1024' hprimitive ⟨0, by omega⟩ hgen
  have hw343' : w < 343 := by omega
  let x : Fin w := ⟨0, by omega⟩
  let d : ℕ := Classical.choose (P.degree_eq_prime_power x)
  have hdegree : w = P.p ^ d := Classical.choose_spec (P.degree_eq_prime_power x)
  have hclassification :=
    primePower_lt343_classification P.p_prime hdegree hw5 hw343'
  by_cases hweven : Even w
  · have hw6 : 6 ≤ w := by
      rcases hweven with ⟨k, hk⟩
      omega
    by_cases hsolvable : IsSolvable (P.complement x)
    · exact primitiveAffineEvenSoluble_rankTailOwnerSourceData
        U hw6 hw1024' hweven hprimitive P hsolvable
    · by_cases hw128 : 128 ≤ w
      · exact PrimitiveAffineNonsolubleSource.canonicalRankTailOwnerSourceData
          hcomp hw128 (by omega) hprimitive P hsolvable
      · have hp2 : P.p = 2 := P.prime_eq_two_of_even_degree x hweven
        have htwo : w = 2 ^ d := by simpa [hp2] using hdegree
        have hsmall := twoPower_lt128_classification htwo hw5 (by omega)
        by_cases h8 : w = 8
        · exact PrimitiveAffineNonsolubleExceptionalSource.rankTailOwnerSourceData
            published.nonsolubleSmall
            U hprimitive P (Or.inl h8) hsolvable
        by_cases h16 : w = 16
        · exact PrimitiveAffineNonsolubleExceptionalSource.rankTailOwnerSourceData
            published.nonsolubleSmall
            U hprimitive P (Or.inr (Or.inl h16)) hsolvable
        by_cases h32 : w = 32
        · exact PrimitiveAffineNonsolubleSmallSource.primitiveAffineNonsolubleSmall_rankTailOwnerSourceData
            hcomp U hprimitive P (Or.inl h32) hsolvable
        · have h64 : w = 64 := by
            rcases hsmall with h | h | h | h
            · exact False.elim (h8 h)
            · exact False.elim (h16 h)
            · exact False.elim (h32 h)
            · exact h
          exact PrimitiveAffineNonsolubleSmallSource.primitiveAffineNonsolubleSmall_rankTailOwnerSourceData
            hcomp U hprimitive P (Or.inr (Or.inr (Or.inl h64))) hsolvable
  by_cases hwprime : w.Prime
  · by_cases hw5eq : w = 5
    · subst w
      exact published.degreeFiveSource U hprimitive P
    · have hw6ne : w ≠ 6 := by
        intro h
        subst w
        norm_num at hwprime
      exact primitiveAffinePrimeDegree_rankTailOwnerSourceData
        U hwprime (by omega) hw1024' hprimitive P hKP
  by_cases h9 : w = 9
  · subst w
    exact primitiveAffineSolubleSmallCentral_rankTailOwnerSourceData
      published.solubleCentral hgen hKP
      U hprimitive P (Or.inl rfl) (published.degreeNineSolvable U P ⟨0, by norm_num⟩)
  by_cases h25 : w = 25
  · subst w
    by_cases hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)
    · exact primitiveAffineSolubleSmallCentral_rankTailOwnerSourceData
        published.solubleCentral hgen hKP
        U hprimitive P (Or.inr rfl) hsolvable
    · exact PrimitiveAffineNonsolubleExceptionalSource.rankTailOwnerSourceData
        published.nonsolubleSmall
        U hprimitive P (Or.inr (Or.inr (Or.inl rfl))) hsolvable
  by_cases h27 : w = 27
  · subst w
    by_cases hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)
    · exact PrimitiveAffineSolubleOddExceptionalSource.rankTailOwnerSourceData
        published.solubleOdd hgen
        U hprimitive P (Or.inl rfl) hsolvable
    · exact PrimitiveAffineNonsolubleExceptionalSource.rankTailOwnerSourceData
        published.nonsolubleSmall
        U hprimitive P (Or.inr (Or.inr (Or.inr rfl))) hsolvable
  by_cases h49 : w = 49
  · subst w
    by_cases hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)
    · exact PrimitiveAffineSolubleOddExceptionalSource.rankTailOwnerSourceData
        published.solubleOdd hgen
        U hprimitive P (Or.inr (Or.inl rfl)) hsolvable
    · exact PrimitiveAffineNonsolubleSmallSource.primitiveAffineNonsolubleSmall_rankTailOwnerSourceData
        hcomp U hprimitive P (Or.inr (Or.inl rfl)) hsolvable
  by_cases h81 : w = 81
  · subst w
    by_cases hsolvable : IsSolvable (P.complement ⟨0, by norm_num⟩)
    · exact PrimitiveAffineSolubleOddExceptionalSource.rankTailOwnerSourceData
        published.solubleOdd hgen
        U hprimitive P (Or.inr (Or.inr rfl)) hsolvable
    · exact PrimitiveAffineNonsolubleSmallSource.primitiveAffineNonsolubleSmall_rankTailOwnerSourceData
        hcomp U hprimitive P (Or.inr (Or.inr (Or.inr rfl))) hsolvable
  by_cases h121 : w = 121
  · exact PrimitiveAffineMediumOddSource.primitiveAffineMediumOdd_rankTailOwnerSourceData
      P hprimitive (Or.inl h121) hgen
  by_cases h125 : w = 125
  · exact PrimitiveAffineMediumOddSource.primitiveAffineMediumOdd_rankTailOwnerSourceData
      P hprimitive (Or.inr (Or.inl h125)) hgen
  by_cases h169 : w = 169
  · exact PrimitiveAffineMediumOddSource.primitiveAffineMediumOdd_rankTailOwnerSourceData
      P hprimitive (Or.inr (Or.inr (Or.inl h169))) hgen
  by_cases h243 : w = 243
  · exact PrimitiveAffineMediumOddSource.primitiveAffineMediumOdd_rankTailOwnerSourceData
      P hprimitive (Or.inr (Or.inr (Or.inr (Or.inl h243)))) hgen
  by_cases h289 : w = 289
  · exact PrimitiveAffineMediumOddSource.primitiveAffineMediumOdd_rankTailOwnerSourceData
      P hprimitive (Or.inr (Or.inr (Or.inr (Or.inr h289)))) hgen
  · exact False.elim (by
      rcases hclassification with h | h | h | h | h | h | h | h | h | h | h | h
      · exact hweven h
      · exact hwprime h
      · exact h9 h
      · exact h25 h
      · exact h27 h
      · exact h49 h
      · exact h81 h
      · exact h121 h
      · exact h125 h
      · exact h169 h
      · exact h243 h
      · exact h289 h)

end PublishedPrimitiveAffineFiniteInput
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
