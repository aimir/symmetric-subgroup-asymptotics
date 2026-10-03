import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveGenericMargin
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitivePrimeMargin
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallExhaustion
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveDegreeTwoExhaustion
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveDegreeThreeExhaustion
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveDegreeFourS4Exhaustion

/-!
# Complete numerical exhaustion of imprimitive affine components

The degree of a literal primitive affine component is a prime power.  Below
twenty-five there are exactly thirteen possibilities.  The preceding
capacity files close every block count in those degrees except for the
explicit finite affine-frame cells recorded here; degree at least twenty-five
is uniform.

This file is only the numerical classifier.  The companion exceptional-cell
bridge must send every value of `ImprimitiveAffineCapacityException` to an
already integrated ambient owner.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Prime-power degrees between two and twenty-four. -/
theorem primePower_two_to_twentyFour_classification
    {r p d : ℕ} (hp : p.Prime) (hr : r = p ^ d)
    (hr2 : 2 ≤ r) (hr25 : r < 25) :
    r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 7 ∨ r = 8 ∨
      r = 9 ∨ r = 11 ∨ r = 13 ∨ r = 16 ∨ r = 17 ∨
      r = 19 ∨ r = 23 := by
  have hd1 : 1 ≤ d := by
    by_contra hd
    have hd0 : d = 0 := by omega
    norm_num [hr, hd0] at hr2
  have hp25 : p < 25 := by
    have hp_le : p ≤ r := by
      calc
        p = p ^ 1 := by simp
        _ ≤ p ^ d := Nat.pow_le_pow_right hp.one_le hd1
        _ = r := hr.symm
    omega
  have hd5 : d < 5 := by
    by_contra hd
    have h5d : 5 ≤ d := by omega
    have hbase : 2 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left hp.two_le 5
    have hexp : p ^ 5 ≤ p ^ d := Nat.pow_le_pow_right hp.one_le h5d
    have : 32 ≤ r := by
      rw [hr]
      norm_num at hbase
      exact hbase.trans hexp
    omega
  subst r
  interval_cases p <;> interval_cases d
  all_goals norm_num at hp
  all_goals norm_num at hr2
  all_goals norm_num at hr25
  all_goals norm_num

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The exact cells not closed by the affine chief-capacity inequality.
Each constructor retains the literal local degree and exact finite
block-count predicate needed by the corresponding physical owner. -/
inductive ImprimitiveAffineCapacityException
    (r s : ℕ) : Prop
  | degreeTwo (hr : r = 2)
      (hs : ComponentSource.IsDegreeTwoAffineExceptionalBlockCount s)
  | degreeThree (hr : r = 3)
      (hs : s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 6 ∨ s = 8 ∨ s = 12 ∨ s = 18)
  | degreeFour (hr : r = 4)
      (hs : ComponentSource.IsDegreeFourTwentyFourExceptionalBlockCount s)
  | degreeFive (hr : r = 5)
      (hs : s = 2 ∨ s = 3 ∨ s = 4)
  | degreeEight (hr : r = 8)
      (hs : s = 2 ∨ s = 4 ∨ s = 6)
  | degreeNine (hr : r = 9)
      (hs : s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 6 ∨ s = 12)
  | degreeSixteen (hr : r = 16)
      (hs : s = 2 ∨ s = 4)

namespace ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

/-- Every imprimitive affine component either has the required literal
chief-capacity margin or belongs to the exact bounded exception type. -/
noncomputable def capacityExhaustion
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (hcomp : PrimitiveCompositionLengthInput) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PLift (ImprimitiveAffineCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)) := by
  by_cases hr25 : 25 ≤ Nat.card block.Fibre
  · exact .inl (of_localDegree_ge_twentyFive hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hcomp hr25)
  have hr25' : Nat.card block.Fibre < 25 := by omega
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree : Nat.card block.Fibre = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  by_cases h2 : Nat.card block.Fibre = 2
  · exact match degreeTwoExhaustion hTraceyHalf hTraceyLog hTraceyRefined
        hTraceyPerm block P h2 with
      | .inl S => .inl S
      | .inr h => .inr ⟨ImprimitiveAffineCapacityException.degreeTwo h2 h.down⟩
  by_cases h3 : Nat.card block.Fibre = 3
  · exact match degreeThreeExhaustion hTraceyHalf hTraceyLog hTraceyRefined
        hTraceyPerm block P h3 with
      | .inl S => .inl S
      | .inr h => .inr ⟨ImprimitiveAffineCapacityException.degreeThree h3 h.down⟩
  by_cases h4 : Nat.card block.Fibre = 4
  · have hdiv := component_card_dvd_24 block P h4
    exact match degreeFourTwentyFourExhaustion hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P h4 hdiv with
      | .inl S => .inl S
      | .inr h => .inr ⟨ImprimitiveAffineCapacityException.degreeFour h4 h.down⟩
  by_cases h5 : Nat.card block.Fibre = 5
  · exact match degreeFiveExhaustion hTraceyHalf hTraceyLog hTraceyRefined
        hTraceyPerm block P h5 with
      | .inl S => .inl S
      | .inr h => .inr ⟨ImprimitiveAffineCapacityException.degreeFive h5 h.down⟩
  by_cases h7 : Nat.card block.Fibre = 7
  · exact .inl (of_primeSeven block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm h7)
  by_cases h8 : Nat.card block.Fibre = 8
  · exact match degreeEightExhaustion hTraceyHalf hTraceyLog hTraceyRefined
        hTraceyPerm block P D h8 with
      | .inl S => .inl S
      | .inr h => .inr ⟨ImprimitiveAffineCapacityException.degreeEight h8 h.down⟩
  by_cases h9 : Nat.card block.Fibre = 9
  · exact match degreeNineExhaustion hTraceyHalf hTraceyLog hTraceyRefined
        hTraceyPerm block P h9 with
      | .inl S => .inl S
      | .inr h => .inr ⟨ImprimitiveAffineCapacityException.degreeNine h9 h.down⟩
  by_cases h11 : Nat.card block.Fibre = 11
  · exact .inl (of_primeElevenToTwentyThree block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm (by rw [h11]; norm_num) (by omega) (by omega))
  by_cases h13 : Nat.card block.Fibre = 13
  · exact .inl (of_primeElevenToTwentyThree block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm (by rw [h13]; norm_num) (by omega) (by omega))
  by_cases h16 : Nat.card block.Fibre = 16
  · exact match degreeSixteenExhaustion hTraceyHalf hTraceyLog hTraceyRefined
        hTraceyPerm block P D h16 with
      | .inl S => .inl S
      | .inr h => .inr ⟨ImprimitiveAffineCapacityException.degreeSixteen h16 h.down⟩
  by_cases h17 : Nat.card block.Fibre = 17
  · exact .inl (of_primeElevenToTwentyThree block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm (by rw [h17]; norm_num) (by omega) (by omega))
  by_cases h19 : Nat.card block.Fibre = 19
  · exact .inl (of_primeElevenToTwentyThree block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm (by rw [h19]; norm_num) (by omega) (by omega))
  by_cases h23 : Nat.card block.Fibre = 23
  · exact .inl (of_primeElevenToTwentyThree block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm (by rw [h23]; norm_num) (by omega) (by omega))
  · have hfalse : False := by
      have hcases := primePower_two_to_twentyFour_classification
        P.p_prime hdegree block.degrees_ge_two.1 hr25'
      rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals contradiction
    exact hfalse.elim

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
