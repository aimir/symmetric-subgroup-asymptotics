import SymmetricSubgroupAsymptotics.DegreeEighteenNineByTwoHead
import SymmetricSubgroupAsymptotics.DegreeEighteenThreeBySixHead
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixChiefPublished
import SymmetricSubgroupAsymptotics.PrimitiveTernaryStrictHeadPublished
import SymmetricSubgroupAsymptotics.SmallTransitiveTernaryHead

/-!
# The complete degree-eighteen ternary head bound

The primitive case is a published bounded-catalogue consequence.  A minimal
block system in the imprimitive case has one of the four orientations
`2 × 9`, `3 × 6`, `6 × 3`, or `9 × 2`.  The middle hard orientation uses
the sharp abelian-kernel descent theorem, while the remaining orientations
use the literal minimal-block recurrence or the full-coordinate theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The retained degree-eighteen input, derived from published primitive
catalogue correspondences and the proved four-orientation imprimitive
analysis. -/
theorem degreeEighteenTernaryHeadBound_of_published
    (catalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (h6 : PublishedPrimitiveDegreeSixClassification)
    (hPrimitive : PrimitiveTernaryStrictHeadBound) :
    DegreeEighteenTernaryHeadBound := by
  intro A Ω _ _ _ _ _ _ _ hDegree N _
  have htwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp htwo
  by_cases hp : MulAction.IsPreprimitive A Ω
  · letI : MulAction.IsPreprimitive A Ω := hp
    have hz := primitive_degreeEighteen_ternaryHead_eq_zero
      catalogue A Ω hDegree N
    omega
  · let ω₀ : Ω := Classical.choice inferInstance
    let D : OriginalMinimalBlock (A := A) ω₀ :=
      Classical.choice (originalMinimalBlock_nonempty ω₀ hp)
    let r := Nat.card D.Fibre
    let s := Nat.card D.Points
    have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
    have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
    have hrs : r * s = 18 := by
      simpa only [r, s, hDegree] using D.degree_product
    have hrle : r ≤ 18 := Nat.le_of_dvd (by decide) ⟨s, hrs.symm⟩
    have hsle : s ≤ 18 := Nat.le_of_dvd (by decide) ⟨r, by
      simpa [Nat.mul_comm] using hrs.symm⟩
    have hfactors :
        (r = 2 ∧ s = 9) ∨ (r = 3 ∧ s = 6) ∨
          (r = 6 ∧ s = 3) ∨ (r = 9 ∧ s = 2) := by
      interval_cases r <;> interval_cases s <;> omega
    letI : Nontrivial D.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp (by simpa only [r] using hr)
    letI : Finite D.Component :=
      Finite.of_surjective
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
    letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
    letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
    letI : FaithfulSMul D.Top D.Points := D.top_faithful
    letI : Finite D.Top := D.top_finite
    let T := originalNormalRange D.topMap N
    rcases hfactors with h29 | h36 | h63 | h92
    · let c := actualChiefSeries D.Component
      have hc : actualChiefSeriesTernaryWeight c = 0 :=
        permutationChiefWeight_eq_zero_of_card_le_two D.Component c (by
          simpa only [r] using h29.1.le)
      have ht := transitive_degreeNine_ternaryHead_le_two hPrimitive T (by
        simpa only [s] using h29.2)
      have hd := D.head_bound_nat N c
      have ht' : Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) ≤ 2 := by
        simpa only [T] using ht
      exact hd.trans (by simpa only [hc, zero_mul, zero_add] using ht')
    · exact D.degreeEighteen_threeBySix_ternaryHead_le_two
        hPrimitive N (by simpa only [r] using h36.1)
          (by simpa only [s] using h36.2)
    · obtain ⟨c, hc⟩ := primitiveDegreeSix_chiefWeight_eq_zero
        h6 D.Component D.Fibre (by simpa only [r] using h63.1)
      have ht := transitive_degreeThree_ternaryHead_le_one T (by
        simpa only [s] using h63.2)
      have hd := D.head_bound_nat N c
      have ht' : Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) ≤ 1 := by
        simpa only [T] using ht
      have hone := hd.trans (by simpa only [hc, zero_mul, zero_add] using ht')
      omega
    · exact D.degreeEighteen_nineByTwo_ternaryHead_le_two
        hPrimitive N (by simpa only [r] using h92.1)
          (by simpa only [s] using h92.2)

end SymmetricSubgroupAsymptotics

end
