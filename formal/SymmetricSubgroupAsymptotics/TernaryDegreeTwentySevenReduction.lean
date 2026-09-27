import SymmetricSubgroupAsymptotics.DegreeTwentySevenClosure
import SymmetricSubgroupAsymptotics.TernaryHighImprimitiveDegrees

/-!
# Exact minimal-block data in the high degree-twenty-seven case

The numerical high-action recurrence orients the only two possible
factorizations of degree twenty seven.  The primitive fibre has degree three,
the faithful top has degree nine, and the original normal top image has exact
ternary relative rank two.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Exact finite degree-nine endpoint needed by the degree-twenty-seven
block reduction.  The committed finite certificate finds precisely the four
transitive actions `9T2`, `9T6`, `9T7`, and `9T17`; each is a 3-group. -/
def DegreeNineRankTwoPGroupInput : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] [Nonempty X],
    Nat.card X = 9 → ∀ (M : Subgroup G) [M.Normal],
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) = 2 →
        IsPGroup 3 G

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω]
variable {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- The high degree-twenty-seven recurrence fixes the literal minimal-block
orientation and the exact rank of the retained normal image in the top. -/
theorem highDegreeTwentySeven_minimalBlock_data
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 27)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nat.card D.Fibre = 3 ∧ Nat.card D.Points = 9 ∧
      Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 2 := by
  letI : Nonempty Ω := ⟨ω₀⟩
  let r := Nat.card D.Fibre
  let s := Nat.card D.Points
  let d := Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)
  let T := originalNormalRange D.topMap N
  let t := Module.finrank (ZMod 3) (primeRelativeCharacters 3 T)
  have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
  have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
  have hrs : r * s = 27 := by
    have hproduct : r * s = Nat.card Ω := by
      simpa only [r, s] using D.degree_product
    exact hproduct.trans hDegree
  have hrdiv : r ∣ 27 := ⟨s, hrs.symm⟩
  have hrle : r ≤ 27 := Nat.le_of_dvd (by decide) hrdiv
  have hrCases : r = 3 ∨ r = 9 := by
    interval_cases r <;> norm_num at hrs ⊢ <;> omega
  letI : Nontrivial D.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by simpa only [r] using hr)
  letI : Finite D.Component :=
    Finite.of_surjective
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
  obtain ⟨c, hc⟩ := hChief D.Component D.Fibre
  let v := actualChiefSeriesTernaryWeight c
  have hv : v ≤ r / 3 := by simpa only [v, r] using hc
  have hd : d ≤ v * ternaryIndexWidth s + t := by
    simpa only [d, v, s, t, T] using D.head_bound_nat N c
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  have ht : t ≤ ternaryStabilityBound s := by
    simpa only [t, s, T] using
      (transitiveTernaryHead_stability hChief hPrimitive h18 T)
  have hdle : d ≤ 5 := by
    have h := transitiveTernaryHead_stability hChief hPrimitive h18
      (A := A) (Ω := Ω) N
    simpa only [d, hDegree, ternaryStabilityBound] using h
  have hHigh' : 81 < 20 * d := by
    simpa only [hDegree, d] using hHigh
  have hdExact : d = 5 := by omega
  rcases hrCases with hr3 | hr9
  · have hrs' : 3 * s = 27 := by simpa only [hr3] using hrs
    have hs9 : s = 9 := by omega
    have hv1 : v ≤ 1 := by simpa only [hr3] using hv
    have ht2 : t ≤ 2 := by
      simpa only [hs9, ternaryStabilityBound_nine] using ht
    have hd' : d ≤ 3 * v + t := by
      simpa only [hs9, ternaryIndexWidth_nine, Nat.mul_comm] using hd
    have htExact : t = 2 := by omega
    exact ⟨by simpa only [r] using hr3,
      by simpa only [s] using hs9,
      by simpa only [t, T] using htExact⟩
  · have hrs' : 9 * s = 27 := by simpa only [hr9] using hrs
    have hs3 : s = 3 := by omega
    have hv3 : v ≤ 3 := by simpa only [hr9] using hv
    have ht1 : t ≤ 1 := by
      simpa only [hs3, ternaryStabilityBound_three] using ht
    have hd' : d ≤ v + t := by
      simpa only [hs3, ternaryIndexWidth_three, mul_one] using hd
    omega

include D in
/-- Once the exact finite degree-nine endpoint is installed, every high
degree-twenty-seven pair on this literal minimal block enters the 3-group
owner. -/
theorem highDegreeTwentySeven_isPGroup
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (h9 : DegreeNineRankTwoPGroupInput)
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 27)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    IsPGroup 3 A := by
  obtain ⟨hFibre, hPoints, hTop⟩ :=
    highDegreeTwentySeven_minimalBlock_data (D := D)
      hChief hPrimitive h18 N hDegree hHigh
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  let T := originalNormalRange D.topMap N
  have hTopGroup : IsPGroup 3 D.Top := h9 D.Top D.Points hPoints T (by
    simpa only [T] using hTop)
  apply D.degreeTwentySeven_high_isPGroup N hDegree hFibre hTopGroup
  · omega
  · exact hHigh

end OriginalMinimalBlock

/-- The degree-twenty-seven branch of the global high-action menu, with the
minimal block chosen internally from the original imprimitive action. -/
theorem highDegreeTwentySeven_imprimitive_isPGroup
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (h9 : DegreeNineRankTwoPGroupInput)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (himprimitive : ¬ MulAction.IsPreprimitive A Ω)
    (hDegree : Nat.card Ω = 27)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    IsPGroup 3 A := by
  have hTwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hTwo
  let ω₀ : Ω := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := A) ω₀ :=
    Classical.choice (originalMinimalBlock_nonempty ω₀ himprimitive)
  exact OriginalMinimalBlock.highDegreeTwentySeven_isPGroup (D := D)
    hChief hPrimitive h18 h9 N hDegree hHigh

end SymmetricSubgroupAsymptotics

end
