import SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedDOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.OriginalNonaffineTwistedDBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity

/-! The whole nonsplit-D one-factor primitive ordinary branch.
Below128 the literal point-radical index leaves binary ranks four/five;
actual root generators and the original outer bound pay both at once. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedDAllDegreeOrdinary
open PrimitiveSocleRawStructure

private theorem bounded_parameters (s q n : ℕ) (hq : 2≤q)
    (hi : (q^(s+2)-1)*q^(s+3)≤n) (hn : n<128) : q=2 ∧ s≤1 ∧ 24≤n := by
  have hq0 : 0<q := by omega
  have ha : 4≤q^(s+2) := by
    exact (Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right hq0 (by omega))
  have hb : 8≤q^(s+3) := by
    exact (Nat.pow_le_pow_left hq 3).trans (Nat.pow_le_pow_right hq0 (by omega))
  have h24 : 24≤n := (Nat.mul_le_mul (show 3≤q^(s+2)-1 by omega) hb).trans hi
  have hq2 : q=2 := by
    by_contra hh
    have hq3 : 3≤q := by omega
    have ha9 : 9≤q^(s+2) :=
      (Nat.pow_le_pow_left hq3 2).trans (Nat.pow_le_pow_right hq0 (by omega))
    have hb27 : 27≤q^(s+3) :=
      (Nat.pow_le_pow_left hq3 3).trans (Nat.pow_le_pow_right hq0 (by omega))
    have hp : 216≤n := (Nat.mul_le_mul (show 8≤q^(s+2)-1 by omega) hb27).trans hi
    omega
  refine ⟨hq2,?_,h24⟩
  by_contra hh
  have hs : 2 ≤ s := by omega
  have ha16 : 16≤q^(s+2) :=
    (Nat.pow_le_pow_left hq 4).trans (Nat.pow_le_pow_right hq0 (by omega))
  have hb32 : 32≤q^(s+3) :=
    (Nat.pow_le_pow_left hq 5).trans (Nat.pow_le_pow_right hq0 (by omega))
  have hp : 480≤n := (Nat.mul_le_mul (show 15≤q^(s+2)-1 by omega) hb32).trans hi
  omega

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount=1)
    (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    (e : D.Simple≃*CFSG.Models.TwistedD r q) :
    MarkedC4.genRank G≤traceyPermutationGeneratorCeiling (Nat.card X) := by
  classical
  by_cases hlarge : 128≤Nat.card X
  · exact PrimitiveSocleTwistedDOneFactorOrdinaryTail.genRank_le_ceiling D hk r hr q e hlarge
  obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+4 := ⟨r-4,by omega⟩
  letI : IsSimpleGroup (CFSG.Models.TwistedD (s+4) q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedD (s+4) q) := Finite.of_equiv D.Simple e.toEquiv
  have hnoncomm : ¬ IsMulCommutative (CFSG.Models.TwistedD (s+4) q) := by
    intro h
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hm := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
  have hi := CFSGReduction.typeTwistedD_point_radical_le_leastProperIndex (s+4) (by omega) q ell hm
  have hd := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hslice : (q.order^(s+2)-1)*q.order^(s+3)≤Nat.card X := by
    simpa only [show s+4-2=s+2 by omega,show s+4-1=s+3 by omega] using hi.trans hd
  obtain ⟨hq,hs,hn24⟩ := bounded_parameters s q.order (Nat.card X)
    (CFSGTwistedAQuadraticTrace.order_two_le q) hslice (by omega)
  have he : q.exponent=1 := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order
    q (by rw [hq]; decide)
  obtain ⟨S,hS,hcard⟩ := CFSGTwistedDRelativeOrdinaryGenerators.original_exists_generating_finset s q
  let U := S.image e.symm
  have hU : Subgroup.closure (U : Set D.Simple)=⊤ := by
    rw [Finset.coe_image]
    change Subgroup.closure (e.symm.toMonoidHom '' (S : Set _))=⊤
    rw [← MonoidHom.map_closure,hS]
    exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hout := CFSGTwistedDOuterCardinality.original_outer_card_le_eight_exponent s q hnoncomm
  have hout8 : Nat.card (Outer D.Simple)≤8 := by
    rw [CFSGReduction.outer_card_congr e]
    simpa only [he,Nat.mul_one] using hout
  have hmu : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))≤3 :=
    SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow _ 3 Nat.card_pos (by omega)
  have hrec := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  by_cases h32 : 32≤Nat.card X
  · have hcard10 : S.card≤10 := by
      exact hcard.trans (show (2*(s+4))*q.exponent≤10 by rw [he]; nlinarith only [hs])
    have hhead : MarkedC4.genRank D.Simple≤10 :=
      (MarkedC4.genRank_le hU).trans (Finset.card_image_le.trans hcard10)
    have h13 : MarkedC4.genRank G≤13 := by omega
    have hb : 13≤traceyPermutationGeneratorCeiling 32 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 32 1 5 13
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h13.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) h32))
  · have hs0 : s=0 := (TwistedDPointRadicalSmallDegreeParameters.parameters s q.order
        (Nat.card X) (CFSGTwistedAQuadraticTrace.order_two_le q) hslice (by omega)).1
    have hcard8 : S.card≤8 := by simpa only [hs0,he,Nat.mul_one] using hcard
    have hhead : MarkedC4.genRank D.Simple≤8 :=
      (MarkedC4.genRank_le hU).trans (Finset.card_image_le.trans hcard8)
    have h11 : MarkedC4.genRank G≤11 := by omega
    have hb : 11≤traceyPermutationGeneratorCeiling 24 :=
      IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 24 1 5 11
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact h11.trans (hb.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hn24))

theorem exists_generating_finset (hk : D.factorCount=1)
    (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    (e : D.Simple≃*CFSG.Models.TwistedD r q) :
    ∃ S : Finset G, Subgroup.closure (S : Set G)=⊤ ∧
      S.card≤traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨S,hcard,hS⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S,hS,hcard.le.trans (genRank_le_ceiling D hk r hr q e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedDAllDegreeOrdinary
