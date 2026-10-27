import SymmetricSubgroupAsymptotics.PrimitiveSimplePolylogRankTools
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexPacketOrTitsSporadic

/-! The SAME actual root generators and proper-index root stars, before
one-factor coarse fitting. No factorCount restriction or current-degree
threshold is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGInfiniteRootSimplePolylogRank
open PrimitiveSocleRawStructure PrimitiveSimplePolylogRankTools
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₇) := Classical.decEq _
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₈) := Classical.decEq _
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

 theorem typeE6_simple_rank (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E6 q)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  letI : IsSimpleGroup (CFSG.Models.E6 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.E6 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨H,hH,he⟩ := (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell).1
  have hfield : q.order^5≤ell :=
    (CFSGReduction.typeE6_field_fifth_le_index q H hH).trans_eq he
  obtain ⟨S,hS,hcard⟩ := CFSGNormTwoPrimePowerOrdinaryGenerators.exists_generating_finset_of_cartan_eq
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos q E6_cartan 0
  have hc : S.card≤4*(q.exponent*5) := hcard.trans (by omega)
  have hh := rank_le_of_roots q 5 ell (by decide) S hS hc hfield
  simpa only [CoprimeNilpotentProductGenerators.genRank_mulEquiv e] using hh

 theorem typeE7_simple_rank (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E7 q)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  letI : IsSimpleGroup (CFSG.Models.E7 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.E7 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨H,hH,he⟩ := (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell).1
  have hfield : q.order^6≤ell :=
    (CFSGReduction.typeE7_field_sixth_le_index q H hH).trans_eq he
  obtain ⟨S,hS,hcard⟩ := CFSGNormTwoPrimePowerOrdinaryGenerators.exists_generating_finset_of_cartan_eq
    CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
    E7_positive_definite CartanMatrix.E₇_off_diag_nonpos q E7_cartan 0
  have hc : S.card≤4*(q.exponent*6) := hcard.trans (by omega)
  have hh := rank_le_of_roots q 6 ell (by decide) S hS hc hfield
  simpa only [CoprimeNilpotentProductGenerators.genRank_mulEquiv e] using hh

 theorem typeE8_simple_rank (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E8 q)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  letI : IsSimpleGroup (CFSG.Models.E8 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.E8 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  obtain ⟨H,hH,he⟩ := (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell).1
  have hfield : q.order^7≤ell :=
    (CFSGReduction.typeE8_field_seventh_le_index q H hH).trans_eq he
  obtain ⟨S,hS,hcard⟩ := CFSGNormTwoPrimePowerOrdinaryGenerators.exists_generating_finset_of_cartan_eq
    CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
    E8_positive_definite CartanMatrix.E₈_off_diag_nonpos q E8_cartan 0
  have hc : S.card≤4*(q.exponent*7) := hcard.trans (by omega)
  have hh := rank_le_of_roots q 7 ell (by decide) S hS hc hfield
  simpa only [CoprimeNilpotentProductGenerators.genRank_mulEquiv e] using hh

 theorem twistedD_simple_rank (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  obtain ⟨s,rfl⟩ : ∃ s : ℕ,r=s+4 := ⟨r-4,by omega⟩
  letI : IsSimpleGroup (CFSG.Models.TwistedD (s+4) q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedD (s+4) q) := Finite.of_equiv D.Simple e.toEquiv
  obtain ⟨S,hS,hcard⟩ := CFSGTwistedDRelativeOrdinaryGenerators.original_exists_generating_finset s q
  obtain ⟨H,hH,he⟩ := (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell).1
  have hfield : q.order^(s+2)≤ell := by
    have hh := CFSGTwistedDProperIndexOrderBudget.typeTwistedD_field_power_le_proper_index
      (s+4) (by omega) q H hH
    simpa only [show s+4-2=s+2 by omega,he] using hh
  have hc : S.card≤4*(q.exponent*(s+2)) := by
    apply hcard.trans
    nlinarith only [Nat.zero_le (s*q.exponent)]
  have hh := rank_le_of_roots q (s+2) ell (by omega) S hS hc hfield
  simpa only [CoprimeNilpotentProductGenerators.genRank_mulEquiv e] using hh

end SymmetricSubgroupAsymptotics.CFSGInfiniteRootSimplePolylogRank
