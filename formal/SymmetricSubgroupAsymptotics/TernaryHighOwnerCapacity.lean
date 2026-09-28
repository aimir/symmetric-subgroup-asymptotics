import SymmetricSubgroupAsymptotics.TernaryHighOwnedActionDegrees
import SymmetricSubgroupAsymptotics.DegreeSixBinaryBlockOwner
import SymmetricSubgroupAsymptotics.DegreeTwelveTopGeometry
import SymmetricSubgroupAsymptotics.C1TernaryPrimeBaseOwner
import SymmetricSubgroupAsymptotics.C1BinaryNineTopOwner

/-!
# Earlier ownership or capacity on the high ternary frontier

The global ternary stability inputs reduce every strict failure of the
`3/20` capacity inequality to degrees three, four, six, nine, twelve or
twenty-seven.  The first, fourth and sixth degrees are already 3-group
owners, degree four is the natural `A₄` owner, degree six has one of the two
intrinsic binary owners, and the two degree-twelve minimal-block orientations
install the prime-base or nine-translation owner.

This file packages that reduction as the exact owner-or-capacity dichotomy
needed by the outside-action recurrence.  The four global stability
propositions remain explicit hypotheses.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The already constructed structural owners which absorb every strict
failure of the ternary `3/20` capacity inequality. -/
def TernaryHighEarlierOwner (A Ω : Type) [Group A] [MulAction A Ω] : Prop :=
  IsPGroup 3 A ∨
    IsNaturalA4Action A Ω ∨
      Nonempty (C1OddIndexTwoOwnerWitness A) ∨
        Nonempty (C1CyclicBinaryModuleOwnerWitness A) ∨
          IsC1TernaryPrimeBaseOwner A ∨
            IsC1BinaryNineTopOwner A Ω

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- Every fibre of the selected transitive block system has the same finite
cardinality as its base fibre. -/
theorem originalBlockFibre_card_eq
    (x : D.Points) :
    Nat.card (originalBlockFibre D.map x) = Nat.card D.Fibre := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A D.base x
  calc
    Nat.card (originalBlockFibre D.map x) =
        Nat.card (originalBlockFibre D.map (a • D.base)) := by rw [ha]
    _ = Nat.card D.Fibre :=
      (Nat.card_congr
        (OriginalBlockSignCoordinates.fibreTransport D.map D.map_equivariant
          a D.base)).symm

/-- The two saturated degree-twelve orientations install their intrinsic
earlier owners, with the original normal subgroup and actual minimal block
system retained. -/
theorem degreeTwelve_high_structuralOwner
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 12)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    IsC1TernaryPrimeBaseOwner A ∨ IsC1BinaryNineTopOwner A Ω := by
  obtain ⟨ω₀, D, c, horient, hc, hTopRank, hRank⟩ :=
    degreeTwelve_high_top_geometry
      hChief hWeight hPrimitive h18 N hDegree hHigh
  letI : Fintype D.Points := Fintype.ofFinite D.Points
  letI : ∀ x : D.Points, Fintype (originalBlockFibre D.map x) :=
    fun x => Fintype.ofFinite (originalBlockFibre D.map x)
  rcases horient with h34 | h43
  · exact Or.inl
      (D.degreeTwelve_primeBase_owner N h34.1 h34.2.2 hRank hTopRank)
  · have hCard : ∀ x : D.Points,
        Nat.card (originalBlockFibre D.map x) = 4 := by
      intro x
      rw [D.originalBlockFibre_card_eq x, h43.1]
    let e : ∀ x : D.Points, Fin 4 ≃ originalBlockFibre D.map x :=
      fun x => (Finite.equivFinOfCardEq (hCard x)).symm
    exact Or.inr
      (D.fourByThree_nineTopOwner N c h43.2.1 h43.2.2 hc
        hTopRank hRank e)

end OriginalMinimalBlock

/-- Under the four named global ternary inputs, every normal residual pair
is accepted by an earlier structural owner or satisfies the exact `3/20`
capacity inequality. -/
theorem ternaryHigh_earlierOwner_or_capacity
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal] :
    TernaryHighEarlierOwner A Ω ∨
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
        3 * Nat.card Ω := by
  by_cases hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)
  · left
    rcases ternaryHigh_action_owned_menu
        hChief hWeight hPrimitive h18 N hHigh with hThree | hA4 | hSix | hTwelve
    · exact Or.inl hThree
    · exact Or.inr (Or.inl hA4)
    · rcases degreeSix_high_structuralOwner
          hPrimitive N hSix hHigh with hOdd | hCyclic
      · exact Or.inr (Or.inr (Or.inl hOdd))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hCyclic)))
    · rcases OriginalMinimalBlock.degreeTwelve_high_structuralOwner
          hChief hWeight hPrimitive h18 N hTwelve hHigh with hPrime | hNine
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hPrime))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hNine))))
  · right
    omega

end SymmetricSubgroupAsymptotics

end
