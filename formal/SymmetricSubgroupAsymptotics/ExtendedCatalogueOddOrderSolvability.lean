import SymmetricSubgroupAsymptotics.CFSGCatalogueWithAxiomMonster
import SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443BinaryFacts
import SymmetricSubgroupAsymptotics.CFSGOddOrderSolvabilityComplete
import SymmetricSubgroupAsymptotics.SolubleSylowNormalizerPrime

/-! Internal classification-target consequences. The parity and extension
induction use no old classification and import no full new Feit-Thompson
catalogue. The actual raw branch supplies binary generation independently.
These are NOT a new public T1 hypothesis or a claimed constructor of the
extended classification target. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueOddOrderSolvability
open CFSGReduction
open CFSGAxiomMonsterY443ElevenGenerators

variable (hclass : CFSGCatalogueWithAxiomMonster.Classification)

include hclass in
theorem simple_even_card (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hn : ¬IsMulCommutative G) : Even (Nat.card G) := by
  obtain ⟨i,e⟩ := CFSGCatalogueWithAxiomMonster.modelWitness hclass G
  cases i with
  | inl i =>
    let e0 : G ≃* i.val.Model := e
    letI : IsSimpleGroup i.val.Model := e0.symm.isSimpleGroup
    have hnon : ¬IsMulCommutative i.val.Model :=
      fun hc => hn ((isMulCommutative_congr e0).mpr hc)
    rw [Nat.card_congr e0.toEquiv]
    exact nonabelian_simple_model_even_card i.val hnon
  | inr u =>
    let e0 : G ≃* MonsterY443Derived := e
    have hnon : ¬IsMulCommutative MonsterY443Derived :=
      fun hc => hn ((isMulCommutative_congr e0).mpr hc)
    rw [Nat.card_congr e0.toEquiv]
    exact CFSGAxiomMonsterY443BinaryFacts.even_card hnon

include hclass in
theorem odd_order_solvable (G : Type) [Group G] [Finite G]
    (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply solvable_of_simple_order_property Odd
    (fun hn hd => Odd.of_dvd_nat hn hd) ?_ G hG
  intro H _ _ _ hH
  by_contra hnon
  exact hH.not_two_dvd_nat (even_iff_two_dvd.mp (simple_even_card hclass H hnon))

include hclass in
theorem oddOrderSolvability : SylowTwoNormalizerOfOddOrderSolvability.OddOrderSolvability :=
  odd_order_solvable hclass

include hclass in
theorem raw_goodSylowTwo [Finite MonsterY443Derived] : GoodSylowPrime MonsterY443Derived 2 :=
  CFSGAxiomMonsterY443BinaryFacts.goodSylowPrime (oddOrderSolvability hclass)

include hclass in
theorem raw_solubleNormalizerPair [Finite MonsterY443Derived] :
    ∃ p, SolubleSylowNormalizerGeneration.SolubleSylowNormalizerPrime MonsterY443Derived p :=
  ⟨2,SolubleSylowNormalizerGeneration.of_goodSylowPrime (raw_goodSylowTwo hclass)⟩

end SymmetricSubgroupAsymptotics.ExtendedCatalogueOddOrderSolvability
