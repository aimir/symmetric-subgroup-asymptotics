import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveCapacityExhaustion
import SymmetricSubgroupAsymptotics.BinaryAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallExhaustionBinarySmallReduced

/-! Isolated binary-small consumer route. Original datatypes, interfaces,
and finite certificate declarations are imported unchanged. Only the
changed consumer declarations and their private helper closure are copied. -/
set_option autoImplicit false

noncomputable section

open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu

namespace PrimitiveAffineImprimitiveBlockTransfer

namespace BinarySmallReduced

namespace ComponentSource

open _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

noncomputable def capacityExhaustion
    (D : BinaryAffineSmallCatalogueData)
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
  · exact match _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.degreeEightExhaustion hTraceyHalf hTraceyLog hTraceyRefined
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
  · exact match _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.BinarySmallReduced.ComponentSource.degreeSixteenExhaustion hTraceyHalf hTraceyLog hTraceyRefined
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

end BinarySmallReduced

end PrimitiveAffineImprimitiveBlockTransfer

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end

