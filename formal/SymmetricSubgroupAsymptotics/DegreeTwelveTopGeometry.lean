import SymmetricSubgroupAsymptotics.DegreeTwelveBlockReduction
import SymmetricSubgroupAsymptotics.TernaryDegreeFourClosure

/-!
# Literal top geometries in the high degree-twelve branch

The saturated minimal-block reduction already gives a rank-one original
normal top image.  On four blocks this forces the literal natural `A₄`
action.  On three blocks it forces a 3-group; faithful transitivity then
forces its order to be exactly three.  These are the two action geometries
needed by the prime-base and `V₄`-block owner arguments.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A finite faithful transitive three-point 3-group has order three. -/
theorem transitiveThreePoint_threePGroup_card
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hDegree : Nat.card X = 3) (hG : IsPGroup 3 G) :
    Nat.card G = 3 := by
  let x : X := Classical.choice (Nat.card_pos_iff.mp (by omega)).1
  have hIndex : (MulAction.stabilizer G x).index = 3 := by
    simpa only [hDegree] using MulAction.index_stabilizer_of_transitive G x
  have hMul := (MulAction.stabilizer G x).card_mul_index
  have hLower : 3 ≤ Nat.card G := by
    have hPos : 0 < Nat.card (MulAction.stabilizer G x) := Nat.card_pos
    rw [hIndex] at hMul
    omega
  have hUpper : Nat.card G ≤ 6 := by
    let e : X ≃ Fin 3 := Finite.equivFinOfCardEq hDegree
    let U := labelledActionImage (A := G) e
    have hU : Nat.card U ≤ 6 := by
      have h := Subgroup.card_le_card_group U
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at h ⊢
      exact h
    calc
      Nat.card G = Nat.card U := Nat.card_congr (faithfulLabelledActionEquiv e).toEquiv
      _ ≤ 6 := hU
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  have hkPos : 0 < k := by
    by_contra h
    have hkZero : k = 0 := by omega
    rw [hkZero, pow_zero] at hk
    omega
  have hkLe : k ≤ 1 := by
    by_contra h
    have hp : 3 ^ 2 ≤ 3 ^ k :=
      Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) (by omega)
    rw [← hk] at hp
    omega
  have hkOne : k = 1 := by omega
  simpa only [hkOne, pow_one] using hk

/-- The full high degree-twelve reduction with the literal top action
identified in both surviving orientations. -/
theorem degreeTwelve_high_top_geometry
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 12)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    ∃ (ω₀ : Ω) (D : OriginalMinimalBlock (A := A) ω₀)
        (c : ActualChiefSeries D.Component),
      ((Nat.card D.Fibre = 3 ∧ Nat.card D.Points = 4 ∧
          IsNaturalA4Action D.Top D.Points) ∨
        (Nat.card D.Fibre = 4 ∧ Nat.card D.Points = 3 ∧
          Nat.card D.Top = 3)) ∧
      actualChiefSeriesTernaryWeight c = 1 ∧
      Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1 ∧
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2 := by
  obtain ⟨ω₀, D, c, horient, hv, ht, hd⟩ :=
    degreeTwelve_high_minimalBlock_data
      hChief hWeight hPrimitive h18 N hDegree hHigh
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  let T := originalNormalRange D.topMap N
  have hTRank : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 T) = 1 := by
    simpa only [T] using ht
  refine ⟨ω₀, D, c, ?_, hv, ht, hd⟩
  rcases horient with h34 | h43
  · exact Or.inl ⟨h34.1, h34.2,
      degreeFour_rankOne_isNaturalA4 h34.2 T hTRank⟩
  · have hP : IsPGroup 3 D.Top :=
      degreeThree_rankOne_isPGroup h43.2 T hTRank
    exact Or.inr ⟨h43.1, h43.2,
      transitiveThreePoint_threePGroup_card h43.2 hP⟩

end SymmetricSubgroupAsymptotics

end
