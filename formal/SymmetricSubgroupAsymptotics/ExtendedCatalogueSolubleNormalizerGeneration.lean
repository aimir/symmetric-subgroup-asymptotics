import SymmetricSubgroupAsymptotics.ExtendedCatalogueClosedNormalizerModels
import SymmetricSubgroupAsymptotics.ExtendedCatalogueOddOrderSolvability

/-! Complete INTERNAL AG successor over the extended actual classifier.
The current remaining12 normalizer callback is unchanged. Odd-order
solvability, closed old model witnesses and raw-Y443 Good2 are constructed
inside the proof; no old CFSG, soluble-generation callback, raw numerical
row, old/new Monster recognition or public classifier parameter is added.
The Classification argument here is the internal construction target only.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueSolubleNormalizerGeneration
open CFSGReduction SolubleSylowNormalizerGeneration
open CFSGAxiomMonsterY443ElevenGenerators

variable (hclass : CFSGCatalogueWithAxiomMonster.Classification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterJankoTwoDihedral i →
        ∃ p,SolubleSylowNormalizerPrime i.Model p)

include hclass remaining in
theorem simple_normalizerPairs (T : Type) [Group T] [Finite T] [IsSimpleGroup T]
    (hn : ¬IsMulCommutative T) : ∃ p,SolubleSylowNormalizerPrime T p := by
  obtain ⟨i,e⟩ := CFSGCatalogueWithAxiomMonster.modelWitness hclass T
  cases i with
  | inl i =>
    let e0 : T ≃* i.val.Model := e
    letI : Finite i.val.Model := Finite.of_equiv T e0.toEquiv
    letI : IsSimpleGroup i.val.Model := e0.symm.isSimpleGroup
    have hnon : ¬IsMulCommutative i.val.Model :=
      fun hc => hn ((isMulCommutative_congr e0).mpr hc)
    obtain ⟨p,hp⟩ := ExtendedCatalogueClosedNormalizerModels.models_of_remaining
      (ExtendedCatalogueOddOrderSolvability.oddOrderSolvability hclass) remaining i.val hnon
    exact ⟨p,SolubleSylowNormalizerGeneration.map e0.symm hp⟩
  | inr u =>
    let e0 : T ≃* MonsterY443Derived := e
    letI : Finite MonsterY443Derived := Finite.of_equiv T e0.toEquiv
    obtain ⟨p,hp⟩ := ExtendedCatalogueOddOrderSolvability.raw_solubleNormalizerPair hclass
    exact ⟨p,SolubleSylowNormalizerGeneration.map e0.symm hp⟩

include hclass remaining in
theorem aschbacherGuralnick : MarkedC4.PublishedAschbacherGuralnickSolubleGeneration :=
  SolubleSylowNormalizerGeneration.aschbacherGuralnick_of_simple_normalizerPairs
    (simple_normalizerPairs hclass remaining)

end SymmetricSubgroupAsymptotics.ExtendedCatalogueSolubleNormalizerGeneration
