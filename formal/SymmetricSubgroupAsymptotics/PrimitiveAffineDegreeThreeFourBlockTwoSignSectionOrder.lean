import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignInvariantParity
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignLiteralStructure

/-!
# Orders of the literal proper ternary sections

Every proper two-sign axis leaves a two-dimensional ternary kernel.  This
file converts that rank statement into the exact kernel order nine and then
uses the actual descended top map to bound the whole section by

`9 * 32 = 288`.

The bound is deliberately proved on the literal quotients.  In particular,
it does not replace the acting top by an abstract binary group and it does
not enumerate the proper normal axes.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev G := preE7NonPairAction w U

/-- A proper retained two-sign section has exactly nine elements. -/
theorem degreeThreeFourBlockTwoSignSectionModule_card_eq_nine
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Nat.card (DegreeThreeFourBlockTwoSignSectionModule block P N) = 9 := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  have hdim : Module.finrank (ZMod P.p)
      (DegreeThreeFourBlockTwoSignSectionModule block P N) = 2 :=
    degreeThreeFourBlockTwoSignSectionModule_finrank_eq_two
      block P hr hs hcomponent hbinary htwo N
  calc
    Nat.card (DegreeThreeFourBlockTwoSignSectionModule block P N) =
        Nat.card (ZMod P.p) ^ Module.finrank (ZMod P.p)
          (DegreeThreeFourBlockTwoSignSectionModule block P N) :=
      Module.natCard_eq_pow_finrank
        (K := ZMod P.p)
        (V := DegreeThreeFourBlockTwoSignSectionModule block P N)
    _ = 3 ^ 2 := by rw [Nat.card_zmod, hp, hdim]
    _ = 9 := by norm_num

/-- The kernel of the literal descended top map has order nine. -/
theorem degreeThreeFourBlockTwoSignSectionBase_ker_card_eq_nine
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Nat.card (degreeThreeFourBlockTwoSignSectionBase block P N).ker = 9 := by
  let C := degreeThreeFourBlockTwoSignSectionQuotientChart block P N
  calc
    Nat.card (degreeThreeFourBlockTwoSignSectionBase block P N).ker =
        Nat.card
          (Multiplicative
            (DegreeThreeFourBlockTwoSignSectionModule block P N)) :=
      Nat.card_congr C.equiv.symm.toEquiv
    _ = Nat.card (DegreeThreeFourBlockTwoSignSectionModule block P N) := rfl
    _ = 9 := degreeThreeFourBlockTwoSignSectionModule_card_eq_nine
      block P hr hs hcomponent hbinary htwo N

/-- Every literal acting top of a proper two-sign section has order at most
thirty two, because it is an actual quotient of the signed four-block
group. -/
theorem degreeThreeFourBlockTwoSignSectionTop_card_le_thirty_two
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Nat.card
      (G ⨸ ((QuotientGroup.mk' (E block P)).ker ⊔
        degreeThreeFourBlockTwoSignSectionAxis block P N)) ≤ 32 := by
  let D := (QuotientGroup.mk' (E block P)).ker ⊔
    degreeThreeFourBlockTwoSignSectionAxis block P N
  have hED : E block P ≤ D := by
    dsimp only [D]
    rw [QuotientGroup.ker_mk']
    exact le_sup_left
  let f : (G ⨸ E block P) →* (G ⨸ D) :=
    QuotientGroup.lift (E block P) (QuotientGroup.mk' D) hED
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective (E block P)
      (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D) hED
  have hcard : Nat.card (G ⨸ D) ≤ Nat.card (G ⨸ E block P) :=
    Nat.card_le_card_of_surjective f hf
  rcases degreeThreeFourBlockTwoSign_signedQuotient_card_cases
    block P hr hs hcomponent hbinary htwo with h | h
  · rw [h] at hcard
    simpa only [D] using hcard.trans (by norm_num : 16 ≤ 32)
  · rw [h] at hcard
    simpa only [D] using hcard

/-- Every proper literal quotient in the two-sign stratum has order at most
`288`.  This is the order hypothesis required by the uniform `2^200`
ternary-section comparison. -/
theorem degreeThreeFourBlockTwoSignSectionQuotient_card_le_two_eighty_eight
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Nat.card
      (G ⨸ degreeThreeFourBlockTwoSignSectionAxis block P N) ≤ 288 := by
  let R := G ⨸ degreeThreeFourBlockTwoSignSectionAxis block P N
  let A := G ⨸ ((QuotientGroup.mk' (E block P)).ker ⊔
    degreeThreeFourBlockTwoSignSectionAxis block P N)
  let pi : R →* A := degreeThreeFourBlockTwoSignSectionBase block P N
  have hkernel : Nat.card pi.ker = 9 :=
    degreeThreeFourBlockTwoSignSectionBase_ker_card_eq_nine
      block P hr hs hcomponent hbinary htwo N
  have htop : Nat.card A ≤ 32 :=
    degreeThreeFourBlockTwoSignSectionTop_card_le_thirty_two
      block P hr hs hcomponent hbinary htwo N
  have hfactor := pi.ker.card_mul_index
  have hindex : pi.ker.index = Nat.card A := by
    rw [Subgroup.index_ker,
      pi.range_eq_top_of_surjective
        (degreeThreeFourBlockTwoSignSectionBase_surjective block P N),
      Nat.card_congr Subgroup.topEquiv.toEquiv]
  rw [hkernel, hindex] at hfactor
  change Nat.card R ≤ 288
  omega

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
