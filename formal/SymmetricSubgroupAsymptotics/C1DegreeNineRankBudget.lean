import SymmetricSubgroupAsymptotics.C1DegreeNineSourceRank

/-!
# The conjugacy-invariant degree-nine source budget

The degree-nine ternary epimorphism estimate uses the retained orbit pattern
only through the numerical inequality `9*d₃(J) ≤ 2*b+3`.  Recording that
inequality as its own source predicate gives the numerical consumer a smaller
and automatically conjugacy-invariant interface.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The exact source inequality needed by the sharp degree-nine row. -/
def C1DegreeNineRankBudget {X : Type}
    (J : Subgroup (Equiv.Perm X)) : Prop :=
  9 * Module.finrank (ZMod 3) (PrimeCharacters 3 J) ≤
    2 * Nat.card X + 3

/-- The one-regular-`C3`, no-natural-`A4` pattern proves the retained
numerical source budget. -/
theorem C1DegreeNineSourcePattern.rankBudget
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Fintype X] (J : Subgroup (Equiv.Perm X))
    (h : C1DegreeNineSourcePattern J) :
    C1DegreeNineRankBudget J := by
  unfold C1DegreeNineRankBudget
  obtain ⟨exceptional, hexceptional, hunique, hnoA4⟩ := h
  exact ternaryCharacterRank_oneExceptionalOrbit J exceptional
    (c1DegreeNineSource_local_capacity hChief hPrimitive h18 J exceptional
      hexceptional hunique hnoA4)

/-- The numerical source budget is unchanged by a physical relabelling of
the complete source. -/
theorem C1DegreeNineRankBudget.map_conj
    {X : Type} [Finite X]
    (J : Subgroup (Equiv.Perm X))
    (h : C1DegreeNineRankBudget J)
    (c : Equiv.Perm X) :
    C1DegreeNineRankBudget
      (J.map (MulAut.conj c).toMonoidHom) := by
  let e : J ≃* J.map (MulAut.conj c).toMonoidHom :=
    (MulAut.conj c).subgroupMap J
  have hrank := primeCharacter_finrank_congr 3 e
  unfold C1DegreeNineRankBudget at h ⊢
  rwa [hrank] at h

end SymmetricSubgroupAsymptotics

end
