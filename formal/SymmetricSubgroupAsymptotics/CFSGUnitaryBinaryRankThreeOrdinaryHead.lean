import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeUpperShear
import SymmetricSubgroupAsymptotics.ShearCoordinateOrdinaryGenerators
import SymmetricSubgroupAsymptotics.GoodSylowSelectedRankOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGUnitaryActualSylowOrdinaryHead
import SymmetricSubgroupAsymptotics.ClassicalClassEquationSmallParameters

/-! The literal binary rank-three unitary upper group has at most four
ordinary generators: two prime-field coordinate lifts, one actual central
kernel generator and the SAME middle shear. Actual GoodSylow generation
then gives a five-generator head on the ORIGINAL model, no pair premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreeOrdinaryHead
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates CFSGUnitaryRankThreeUpperShear

theorem upper_genRank_le_four (q : CFSG.PrimePower) (hq : q.order = 2) :
    MarkedC4.genRank (naturalUnipotent 3 q) ≤ 4 := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
  have hdim : Module.finrank (ZMod q.prime) (q.Extension 2) = 2 := by
    rw [GaloisField.finrank q.prime (Nat.mul_ne_zero (by decide) q.exponent_pos.ne'),he]
  let b : Module.Basis (Fin 2) (ZMod q.prime) (q.Extension 2) :=
    Module.finBasisOfFinrankEq (ZMod q.prime) (q.Extension 2) hdim
  have hh := ShearCoordinateOrdinaryGenerators.genRank_le q.prime 2 b
    (radicalUpperHom q 1) (fixedRadicalParameterHom q 1)
    (fixedRadicalParameterHom_surjective q 1) (middleGenerator q) (radicalConjugate q)
    (conjugate_apply q) (parameter_conjugate q) (generator_generate_of_binary q hq)
  change MarkedC4.genRank (naturalUnipotent 3 q) ≤
    2+MarkedC4.genRank (fixedRadicalParameterHom q 1).ker+1 at hh
  have hker := FiniteGroupPrimeMultiplicityGenerators.genRank_le_cardFactors
    (fixedRadicalParameterHom q 1).ker
  rw [fixedRadicalParameterHom_kernel_card,hq] at hker
  have htwo : ArithmeticFunction.cardFactors 2 = 1 := by decide +kernel
  rw [htwo] at hker
  omega

theorem model_genRank_le_five (q : CFSG.PrimePower) (hq : q.order = 2) :
    MarkedC4.genRank (CFSG.Models.TwistedA 3 q) ≤ 5 := by
  letI : Finite (Fixed 3 q) := originalFixed_finite q 3 (by omega)
  let A := commutator (Fixed 3 q)
  let U := originalUnipotent 3 q
  have hUA : U ≤ A := originalUnipotent_le_derived q 0
  let P : Sylow q.prime A :=
    (originalSylow q 3 (by omega)).subtype (originalSylow_le_derived q 0)
  let eP : P ≃* naturalUnipotent 3 q :=
    (U.subgroupOfEquivOfLe hUA).trans
      (MonoidHom.ofInjective (unipotentToOriginalFixed_injective 3 (by omega) q)).symm
  have hP : MarkedC4.genRank P ≤ 4 := by
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv eP]
    exact upper_genRank_le_four q hq
  have hh := GoodSylowSelectedRankOrdinaryGenerators.genRank_le_of_surjective q.prime
    (originalDerived_goodSylowPrime q 0) P (QuotientGroup.mk' (Subgroup.center A))
    (QuotientGroup.mk'_surjective _)
  exact hh.trans (Nat.add_le_add_right hP 1)

theorem exists_generating_finset (q : CFSG.PrimePower) (hq : q.order = 2) :
    ∃ S : Finset (CFSG.Models.TwistedA 3 q), Subgroup.closure (S : Set (CFSG.Models.TwistedA 3 q)) = ⊤ ∧ S.card ≤ 5 := by
  letI : Finite (Fixed 3 q) := originalFixed_finite q 3 (by omega)
  letI : Finite (CFSG.Models.TwistedA 3 q) := by
    change Finite (commutator (Fixed 3 q) ⧸ Subgroup.center (commutator (Fixed 3 q)))
    infer_instance
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := CFSG.Models.TwistedA 3 q)
  exact ⟨S,hgen,hcard.le.trans (model_genRank_le_five q hq)⟩

end SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreeOrdinaryHead
