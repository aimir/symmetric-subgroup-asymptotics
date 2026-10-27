import SymmetricSubgroupAsymptotics.PrimitiveEightOrdinaryGeneratorsFromCanonicalCoverage
import SymmetricSubgroupAsymptotics.NonaffineFivePointOrdinaryGeneratorsWithoutIndexInput
import SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction

/-! Genuine narrowing of the independent globally minimal failed action.
No conclusion about the original affine group or its strict IH is used.
The two unresolved primitive degrees are explicitly retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.EightPointMinimalFailureDegreeSixOrSeven
open EightPointHalfDegreeFiniteModelReduction

private theorem degree_ne_four (w : PrimitiveSporadicCounterexample 8) : w.degree ≠ 4 := by
  rcases w with ⟨d,hlo,hhi,J,ht,hp,hbad,hmin,D,s,e⟩
  change d ≠ 4
  intro hd
  subst d
  have hr := SmallFourPointOrdinaryGenerators.subgroup_genRank_le_two J
  omega

private theorem degree_ne_five (w : PrimitiveSporadicCounterexample 8) : w.degree ≠ 5 := by
  rcases w with ⟨d,hlo,hhi,J,ht,hp,hbad,hmin,D,s,e⟩
  change d ≠ 5
  intro hd
  subst d
  have hr := NonaffineFivePointOrdinaryGeneratorsWithoutIndexInput.genRank_le_two J D
  omega

private theorem degree_ne_eight (w : PrimitiveSporadicCounterexample 8) : w.degree ≠ 8 := by
  rcases w with ⟨d,hlo,hhi,J,ht,hp,hbad,hmin,D,s,e⟩
  change d ≠ 8
  intro hd
  subst d
  have hr := PrimitiveEightOrdinaryGeneratorsFromCanonicalCoverage.genRank_le_three J hp
  omega

theorem degree_eq_six_or_seven (w : PrimitiveSporadicCounterexample 8) :
    w.degree=6 ∨ w.degree=7 := by
  have h4 := degree_ne_four w
  have h5 := degree_ne_five w
  have h8 := degree_ne_eight w
  have hlo := w.degree_ge_four
  have hhi := w.degree_le
  omega

end SymmetricSubgroupAsymptotics.EightPointMinimalFailureDegreeSixOrSeven
