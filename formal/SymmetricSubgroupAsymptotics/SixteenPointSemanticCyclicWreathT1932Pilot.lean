import SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicWreathSubgroupSource
import SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetPilot

/-! Literal16T1932 pilot through the universal actual-subgroup route.
The proof uses its original physical generators and block map, and does
not use the old independent Singer or coordinate-projector hypotheses. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicWreathT1932Pilot
open BinaryPlaneWreathIrreducible
open Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles

abbrev K := SixteenPointSemanticCyclicQuartetPilot.K
abbrev index := PrimitiveAffineDegreeTwoNonbinary16T1932ActualImportedRow.index

theorem nonbinary : ¬ IsPGroup 2 K := by
  intro hK
  exact PrimitiveAffineDegreeTwoNonbinary16T1932Physical.nonbinary
    (hK.of_surjective SixteenPointSemanticCyclicQuartetPilot.originalMap
      SixteenPointSemanticCyclicQuartetPilot.originalMap_surjective)

theorem blocks_binary : IsPGroup 2 Blocks := by
  have hdiv : Nat.card Blocks∣2^2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by decide +kernel : (finRotate 4)^4=1)
  obtain ⟨n,_,hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  exact IsPGroup.of_card hn

theorem block_projection_surjective : Function.Surjective
    ((PermutationalWreathProduct.rightHom : Lin →* Blocks).comp
      ((SemidirectProduct.rightHom : Affine →* Lin).comp K.subtype)) := by
  intro r
  obtain ⟨l,hl⟩ := SixteenPointSemanticCyclicQuartetPilot.beta_surjective r
  obtain ⟨g,hg⟩ := l.property
  refine ⟨g,?_⟩
  change (g : Affine).right=(l : Lin) at hg
  change (g : Affine).right.right=r
  rw [hg]
  exact hl

/-- Complete original-weight source, through the new arbitrary-correlated
kernel constructor; no final numerical or quotient-socle premise. -/
def source (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7RankTailSourceOrYonedaTopData 16 index :=
  SixteenPointSemanticCyclicWreathSubgroupSource.source K nonbinary block_projection_surjective
    PrimitiveAffineDegreeTwoNonbinary16T1932QuotientSocles.rotation 0 blocks_cycle blocks_binary
    index SixteenPointSemanticCyclicQuartetPilot.actualMap
    SixteenPointSemanticCyclicQuartetPilot.actualMap_surjective hMN hZmud

end SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicWreathT1932Pilot
