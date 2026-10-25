import SymmetricSubgroupAsymptotics.CFSGUnitaryRankFourUpperShear
import SymmetricSubgroupAsymptotics.FrattiniThreeCoordinateShearOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreeFrattiniHead

/-! The actual binary rank-four upper group needs at most six ordinary
generators: four prime-field radical lifts and two middle generators.
The literal ambient Frattini kernel and checked middle shear supply the
missing radical axis. The ORIGINAL model consequently has head7. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankFourOrdinaryHead
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates CFSGUnitaryRankFourUpperShear

theorem upper_genRank_le_six (q : CFSG.PrimePower) (hq : q.order = 2) :
    MarkedC4.genRank (naturalUnipotent 4 q) ≤ 6 := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
  have hdim : Module.finrank (ZMod q.prime) (q.Extension 2) = 2 := by
    rw [GaloisField.finrank q.prime (Nat.mul_ne_zero (by decide) q.exponent_pos.ne'),he]
  let b : Module.Basis (Fin 2) (ZMod q.prime) (q.Extension 2) :=
    Module.finBasisOfFinrankEq (ZMod q.prime) (q.Extension 2) hdim
  obtain ⟨S,hcard,hS⟩ := MarkedC4.genRank_spec (G := naturalUnipotent 2 q)
  have hmiddle : MarkedC4.genRank (naturalUnipotent 2 q) ≤ 2 := by
    simpa only [he,Nat.mul_one] using
      CFSGUnitaryRadicalFrattiniOrdinaryGenerators.rank_two_upper_genRank_le q
  have hS2 : S.card ≤ 2 := hcard.le.trans hmiddle
  have hh := FrattiniThreeCoordinateShearOrdinaryGenerators.genRank_le q.prime 2 b
    (radicalUpperHom q 2) (fixedRadicalParameterHom q 2)
    (fixedRadicalParameterHom_surjective q 2) (middleUnipotentHom q 2) S hS
    (middleShear q hq) (radicalConjugate q hq) (conjugate_apply q hq)
    (parameter_conjugate q hq) (ranges_generate q) (radical_kernel_image_mem_frattini q 2)
  change MarkedC4.genRank (naturalUnipotent 4 q) ≤ 2*2+S.card at hh
  omega

theorem model_genRank_le_seven (q : CFSG.PrimePower) (hq : q.order = 2) :
    MarkedC4.genRank (CFSG.Models.TwistedA 4 q) ≤ 7 := by
  letI : Finite (Fixed 4 q) := originalFixed_finite q 4 (by omega)
  let A := commutator (Fixed 4 q)
  let U := originalUnipotent 4 q
  have hUA : U ≤ A := originalUnipotent_le_derived q 1
  let P : Sylow q.prime A :=
    (originalSylow q 4 (by omega)).subtype (originalSylow_le_derived q 1)
  let eP : P ≃* naturalUnipotent 4 q :=
    (U.subgroupOfEquivOfLe hUA).trans
      (MonoidHom.ofInjective (unipotentToOriginalFixed_injective 4 (by omega) q)).symm
  have hP : MarkedC4.genRank P ≤ 6 := by
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv eP]
    exact upper_genRank_le_six q hq
  have hh := GoodSylowSelectedRankOrdinaryGenerators.genRank_le_of_surjective q.prime
    (originalDerived_goodSylowPrime q 1) P (QuotientGroup.mk' (Subgroup.center A))
    (QuotientGroup.mk'_surjective _)
  exact hh.trans (Nat.add_le_add_right hP 1)

theorem exists_generating_finset (q : CFSG.PrimePower) (hq : q.order = 2) :
    ∃ S : Finset (CFSG.Models.TwistedA 4 q), Subgroup.closure (S : Set (CFSG.Models.TwistedA 4 q)) = ⊤ ∧ S.card ≤ 7 := by
  letI : Finite (Fixed 4 q) := originalFixed_finite q 4 (by omega)
  letI : Finite (CFSG.Models.TwistedA 4 q) := by
    change Finite (commutator (Fixed 4 q) ⧸ Subgroup.center (commutator (Fixed 4 q)))
    infer_instance
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := CFSG.Models.TwistedA 4 q)
  exact ⟨S,hgen,hcard.le.trans (model_genRank_le_seven q hq)⟩

end SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankFourOrdinaryHead
