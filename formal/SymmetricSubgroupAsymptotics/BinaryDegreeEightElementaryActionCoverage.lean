import SymmetricSubgroupAsymptotics.BinaryDegreeEightProperCoverage
import SymmetricSubgroupAsymptotics.BinarySquareActionStructure

/-! A literal elementary binary transitive action on eight points is
point-conjugate to the original regular8T3 action. The checked26-row
coverage is used only at degree8. Each excluded row has an actual
original generator or generator-pair square obstruction. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightElementaryActionCoverage

private def tupleSquareTest {r : ℕ} (g : Fin r → Equiv.Perm (Fin 8)) : Prop :=
  (∀ i x, g i (g i x) = x) ∧
    ∀ i j x, (g i * g j) ((g i * g j) x) = x

private theorem tupleSquareTest_of_closure_squares {r : ℕ}
    (g : Fin r → Equiv.Perm (Fin 8))
    (h : ∀ a : Subgroup.closure (Set.range g), a ^ 2 = 1) : tupleSquareTest g := by
  constructor
  · intro i x
    have he := congrArg (fun a : Subgroup.closure (Set.range g) =>
      (a : Equiv.Perm (Fin 8)) x) (h (closureGenerators g i))
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using he
  · intro i j x
    have he := congrArg (fun a : Subgroup.closure (Set.range g) =>
      (a : Equiv.Perm (Fin 8)) x) (h (closureGenerators g i * closureGenerators g j))
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using he

theorem elementary_action_conjugate_regular
    (G : Subgroup (Equiv.Perm (Fin 8))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 8, ∃ g : G, g.val x = y)
    (hel : BinarySquareActionStructure.SquaresActTrivially (G := G) (X := Fin 8)) :
    ∃ g : Equiv.Perm (Fin 8), MulAut.conj g • G =
      Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) := by
  have ht : PermutationSubgroupTransitive G := by
    intro x y
    obtain ⟨g, hg⟩ := htrans x y
    exact ⟨g.val, g.property, hg⟩
  obtain ⟨i, g, hg⟩ := BinaryActionRegistry8.complete G hG ht
  let e := actionConjugacyEquiv g hg
  have hsquare (u : G) : u ^ 2 = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    exact hel u
  have hrow : ∀ a : BinaryActionRegistry8.actions i, a ^ 2 = 1 := by
    intro a
    obtain ⟨u, rfl⟩ := e.surjective a
    rw [← map_pow, hsquare, map_one]
  fin_cases i
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T1.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T1.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T2.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T2.generators) ht)
  · exact ⟨g, hg⟩
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T4.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T4.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T5.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T5.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T6.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T6.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T7.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T7.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T8.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T8.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T9.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T9.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T10.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T10.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T11.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T11.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T15.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T15.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T16.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T16.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T17.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T17.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T18.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T18.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T19.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T19.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T20.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T20.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T21.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T21.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T22.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T22.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T26.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T26.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T27.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T27.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T28.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T28.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T29.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T29.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T30.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T30.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T31.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T31.generators) ht)
  · have ht := tupleSquareTest_of_closure_squares BinaryMenuCayley8T35.generators hrow
    exact False.elim ((by unfold tupleSquareTest; decide +kernel : ¬ tupleSquareTest BinaryMenuCayley8T35.generators) ht)

end SymmetricSubgroupAsymptotics.BinaryDegreeEightElementaryActionCoverage
