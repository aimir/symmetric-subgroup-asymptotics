import SymmetricSubgroupAsymptotics.TransitiveTernaryStability
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import SymmetricSubgroupAsymptotics.PermutationChiefWeight
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage

/-!
# Direct ternary relative-head bounds in degrees two, three, six and nine

These small endpoints are proved directly from an actual minimal block.
They do not invoke the degree-eighteen bypass and can therefore be used in
its proof without a circular dependency.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem transitive_degreeTwo_ternaryHead_eq_zero
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal] (hdegree : Nat.card Ω = 2) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 0 := by
  let e : Ω ≃ Fin 2 := Finite.equivFinOfCardEq hdegree
  let U : Subgroup (Equiv.Perm (Fin 2)) := labelledActionImage (A := A) e
  let M : Subgroup U := labelledActionNormal e N
  letI : M.Normal := originalNormalRange_normal (labelledActionHom e) N
  have hz := permutationRelativeHead_eq_zero_of_card_le_two U M (by simp)
  rw [labelledActionNormal_head e 3 N]
  exact hz

theorem transitive_degreeThree_ternaryHead_le_one
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal] (hdegree : Nat.card Ω = 3) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 1 := by
  let e : Ω ≃ Fin 3 := Finite.equivFinOfCardEq hdegree
  let U : Subgroup (Equiv.Perm (Fin 3)) := labelledActionImage (A := A) e
  let M : Subgroup U := labelledActionNormal e N
  letI : M.Normal := originalNormalRange_normal (labelledActionHom e) N
  rw [labelledActionNormal_head e 3 N]
  exact permutationRelativeHead_le_one_of_card_le_five U M (by simp)

/-- Every faithful transitive degree-six normal pair has ternary relative
head at most one. -/
theorem transitive_degreeSix_ternaryHead_le_one
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal] (hdegree : Nat.card Ω = 6) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 1 := by
  have htwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp htwo
  by_cases hp : MulAction.IsPreprimitive A Ω
  · letI : MulAction.IsPreprimitive A Ω := hp
    have h := hPrimitive A Ω (by omega) (by omega) (by omega) N
    omega
  · let ω₀ : Ω := Classical.choice inferInstance
    let D : OriginalMinimalBlock (A := A) ω₀ :=
      Classical.choice (originalMinimalBlock_nonempty ω₀ hp)
    let r := Nat.card D.Fibre
    let s := Nat.card D.Points
    have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
    have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
    have hrs : r * s = 6 := by
      simpa only [r, s, hdegree] using D.degree_product
    have hrle : r ≤ 6 := Nat.le_of_dvd (by decide) ⟨s, hrs.symm⟩
    have hsle : s ≤ 6 := Nat.le_of_dvd (by decide) ⟨r, by
      simpa [Nat.mul_comm] using hrs.symm⟩
    have hfactors : (r = 2 ∧ s = 3) ∨ (r = 3 ∧ s = 2) := by
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
    rcases hfactors with h23 | h32
    · let c := actualChiefSeries D.Component
      have hc : actualChiefSeriesTernaryWeight c = 0 :=
        permutationChiefWeight_eq_zero_of_card_le_two D.Component c (by
          simpa only [r] using h23.1.le)
      have ht := transitive_degreeThree_ternaryHead_le_one T (by
        simpa only [s] using h23.2)
      have h := D.head_bound_nat N c
      have ht' : Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) ≤ 1 := by
        simpa only [T] using ht
      exact h.trans (by simpa only [hc, zero_mul, zero_add] using ht')
    · let c := actualChiefSeries D.Component
      have hc : actualChiefSeriesTernaryWeight c ≤ 1 :=
        permutationChiefWeight_le_one_of_card_le_five D.Component c (by
          simpa only [r] using h32.1.le.trans (by decide : 3 ≤ 5))
      have ht := transitive_degreeTwo_ternaryHead_eq_zero T (by
        simpa only [s] using h32.2)
      have h := D.head_bound_nat N c
      have ht' : Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 0 := by
        simpa only [T] using ht
      have hsCard : Nat.card D.Points = 2 := by
        simpa only [s] using h32.2
      exact h.trans (by
        rw [ht', hsCard, ternaryIndexWidth_two, mul_one, add_zero]
        exact hc)

/-- Every faithful transitive degree-nine normal pair has ternary relative
head at most two, independently of the degree-eighteen theorem. -/
theorem transitive_degreeNine_ternaryHead_le_two
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal] (hdegree : Nat.card Ω = 9) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 2 := by
  have htwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp htwo
  by_cases hp : MulAction.IsPreprimitive A Ω
  · letI : MulAction.IsPreprimitive A Ω := hp
    have h := hPrimitive A Ω (by omega) (by omega) (by omega) N
    omega
  · let ω₀ : Ω := Classical.choice inferInstance
    let D : OriginalMinimalBlock (A := A) ω₀ :=
      Classical.choice (originalMinimalBlock_nonempty ω₀ hp)
    let r := Nat.card D.Fibre
    let s := Nat.card D.Points
    have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
    have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
    have hrs : r * s = 9 := by
      simpa only [r, s, hdegree] using D.degree_product
    have hrle : r ≤ 9 := Nat.le_of_dvd (by decide) ⟨s, hrs.symm⟩
    have hr3 : r = 3 := by
      interval_cases r <;> omega
    have hs3 : s = 3 := by
      rw [hr3] at hrs
      omega
    letI : Nontrivial D.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp (by simpa only [r] using hr)
    letI : Finite D.Component :=
      Finite.of_surjective
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
        (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
    let c := actualChiefSeries D.Component
    have hc : actualChiefSeriesTernaryWeight c ≤ 1 :=
      permutationChiefWeight_le_one_of_card_le_five D.Component c (by
        simpa only [r, hr3] using (by decide : 3 ≤ 5))
    letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
    letI : FaithfulSMul D.Top D.Points := D.top_faithful
    letI : Finite D.Top := D.top_finite
    let T := originalNormalRange D.topMap N
    have ht := transitive_degreeThree_ternaryHead_le_one T (by
      simpa only [s, hs3])
    have h := D.head_bound_nat N c
    have ht' : Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) ≤ 1 := by
      simpa only [T] using ht
    have hsCard : Nat.card D.Points = 3 := by
      simpa only [s] using hs3
    exact h.trans (by
      rw [hsCard, ternaryIndexWidth_three, mul_one]
      omega)

end SymmetricSubgroupAsymptotics

end
