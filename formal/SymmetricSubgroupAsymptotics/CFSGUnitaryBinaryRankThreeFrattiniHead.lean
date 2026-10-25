import SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreeOrdinaryHead
import SymmetricSubgroupAsymptotics.FrattiniShearCoordinateOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralCommutators
import SymmetricSubgroupAsymptotics.PrimeFrattini

/-! The actual radical's central kernel consists of commutators in the
SAME finite unitary upper p-group, so lies in its Frattini subgroup.
The two prime-field lifts and the literal middle shear therefore give
three upper generators and four generators on the ORIGINAL model. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreeFrattiniHead
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates CFSGUnitaryRankThreeUpperShear

theorem radical_kernel_image_mem_frattini (q : CFSG.PrimePower)
    (z : fixedRadical q 1) (hz : z ∈ (fixedRadicalParameterHom q 1).ker) :
    radicalUpperHom q 1 z ∈ frattini (naturalUnipotent 3 q) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hcard : Nat.card (naturalUnipotent 3 q) = q.prime^(q.exponent*6) := by
    rw [naturalUnipotent_card]
    change (q.prime^q.exponent)^6 = q.prime^(q.exponent*6)
    rw [pow_mul]
  have hp : IsPGroup q.prime (naturalUnipotent 3 q) := IsPGroup.of_card hcard
  have hcomm : commutator (naturalUnipotent 3 q) ≤ frattini (naturalUnipotent 3 q) := by
    rw [←primeAbelianizationGroupMap_ker q.prime (naturalUnipotent 3 q) hp]
    exact Abelianization.commutator_subset_ker _
  obtain ⟨c,hc⟩ := exists_centralRadical_of_parameter_one q 1 z hz
  obtain ⟨x,y,hxy⟩ := centralRadical_eq_commutator q 1 c
  have he : radicalUpperHom q 1 z =
      ⁅radicalUpperHom q 1 x,radicalUpperHom q 1 y⁆ := by
    rw [←map_commutatorElement,hxy,hc]
  rw [he]
  exact hcomm (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem upper_genRank_le_three (q : CFSG.PrimePower) (hq : q.order = 2) :
    MarkedC4.genRank (naturalUnipotent 3 q) ≤ 3 := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
  have hdim : Module.finrank (ZMod q.prime) (q.Extension 2) = 2 := by
    rw [GaloisField.finrank q.prime (Nat.mul_ne_zero (by decide) q.exponent_pos.ne'),he]
  let b : Module.Basis (Fin 2) (ZMod q.prime) (q.Extension 2) :=
    Module.finBasisOfFinrankEq (ZMod q.prime) (q.Extension 2) hdim
  exact FrattiniShearCoordinateOrdinaryGenerators.genRank_le q.prime 2 b
    (radicalUpperHom q 1) (fixedRadicalParameterHom q 1)
    (fixedRadicalParameterHom_surjective q 1) (middleGenerator q) (radicalConjugate q)
    (conjugate_apply q) (parameter_conjugate q) (generator_generate_of_binary q hq)
    (radical_kernel_image_mem_frattini q)

theorem model_genRank_le_four (q : CFSG.PrimePower) (hq : q.order = 2) :
    MarkedC4.genRank (CFSG.Models.TwistedA 3 q) ≤ 4 := by
  letI : Finite (Fixed 3 q) := originalFixed_finite q 3 (by omega)
  let A := commutator (Fixed 3 q)
  let U := originalUnipotent 3 q
  have hUA : U ≤ A := originalUnipotent_le_derived q 0
  let P : Sylow q.prime A :=
    (originalSylow q 3 (by omega)).subtype (originalSylow_le_derived q 0)
  let eP : P ≃* naturalUnipotent 3 q :=
    (U.subgroupOfEquivOfLe hUA).trans
      (MonoidHom.ofInjective (unipotentToOriginalFixed_injective 3 (by omega) q)).symm
  have hP : MarkedC4.genRank P ≤ 3 := by
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv eP]
    exact upper_genRank_le_three q hq
  have hh := GoodSylowSelectedRankOrdinaryGenerators.genRank_le_of_surjective q.prime
    (originalDerived_goodSylowPrime q 0) P (QuotientGroup.mk' (Subgroup.center A))
    (QuotientGroup.mk'_surjective _)
  exact hh.trans (Nat.add_le_add_right hP 1)

theorem exists_generating_finset (q : CFSG.PrimePower) (hq : q.order = 2) :
    ∃ S : Finset (CFSG.Models.TwistedA 3 q), Subgroup.closure (S : Set (CFSG.Models.TwistedA 3 q)) = ⊤ ∧ S.card ≤ 4 := by
  letI : Finite (Fixed 3 q) := originalFixed_finite q 3 (by omega)
  letI : Finite (CFSG.Models.TwistedA 3 q) := by
    change Finite (commutator (Fixed 3 q) ⧸ Subgroup.center (commutator (Fixed 3 q)))
    infer_instance
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := CFSG.Models.TwistedA 3 q)
  exact ⟨S,hgen,hcard.le.trans (model_genRank_le_four q hq)⟩

end SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreeFrattiniHead
