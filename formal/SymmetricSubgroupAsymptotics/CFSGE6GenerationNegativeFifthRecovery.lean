import SymmetricSubgroupAsymptotics.CFSGE6GenerationFarMixedSign
import SymmetricSubgroupAsymptotics.CFSGE6GenerationFarExtraction
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWordRootTransport

/-! The far mixed line is the ORIGINAL negative fifth simple-root line,
up to an integral unit parameter. Generated-Lie recognition and primitive
integer conjugation prove the sign before all-characteristic transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationNegativeFifthRecovery
open CFSGE6GenerationTorusPilot CFSGE6GenerationExtractionPilot
open CFSGE6GenerationFarFactors CFSGE6GenerationFarExtraction
open CFSGE6GenerationFarMixedSign CFSGE6GenerationFarMixedSimpleLine
open CFSGE6GenerationBranchLattice CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoGeckIntegralWord CFSGSerreQuadraticWordRootTransport
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

theorem exists_far_mixed_negative_identity (K : Type) [Field K] :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧ ∀a : K,
      farMixed K a=canonicalRoot e6Data K true 5 ((ε:K)*a) := by
  obtain ⟨ε,hε,hc⟩ := exists_coefficient_sign
  have hwQ := word_eq_canonicalWord CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index ℚ farMixedWord
  have hc' : (canonicalWord e6Data ℚ farMixedWord : Matrix Index Index ℚ)*
      fieldRoot e6Data ℚ false 3*
      (((canonicalWord e6Data ℚ farMixedWord)⁻¹ : Ambient ℚ) : Matrix Index Index ℚ)=
      (ε:ℚ) • fieldRoot e6Data ℚ true 5 := by
    rw [←hwQ]
    simpa only [farCoefficient,CFSGNormTwoGeckRationalWeylCollecting.rational_F_eq] using hc
  have hr (a : ℚ) : rootWord e6Data ℚ farMixedWord false 3 a=
      canonicalRoot e6Data ℚ true 5 ((ε:ℚ)*a) :=
    rational_scaled_root e6Data (canonicalWord e6Data ℚ farMixedWord) false true 3 5 (ε:ℚ) hc' a
  refine ⟨ε,hε,?_⟩
  intro a
  have hf := far_mixed_as_word K a
  rw [word_eq_canonicalWord] at hf
  exact hf.trans (word_root_of_rational e6Data K farMixedWord false true 3 5 ε hr a)

theorem pair_recovers_negative_fifth (K : Type) [Field K] [Finite K]
    (hcard : 3≤Nat.card K) (g : Kˣ) (hg : ∀u : Kˣ,u∈Subgroup.zpowers g) :
    ∀a : K,canonicalRoot e6Data K true 5 a∈pairGroup K g := by
  obtain ⟨ε,hε,hid⟩ := exists_far_mixed_negative_identity K
  intro a
  rcases hε with hε|hε
  · have hh := pair_recovers_far_mixed K hcard g hg a
    rw [hid] at hh
    simpa only [hε,Int.cast_one,one_mul] using hh
  · have hh := pair_recovers_far_mixed K hcard g hg (-a)
    rw [hid] at hh
    simpa only [hε,Int.cast_neg,Int.cast_one,neg_one_mul,neg_neg] using hh

theorem exists_actual_pair_recovering_negative_fifth (K : Type) [Field K] [Finite K]
    (hcard : 3≤Nat.card K) : ∃g : Kˣ,
      pairGroup K g≤canonicalElementaryGroup e6Data K ∧
      ∀a : K,canonicalRoot e6Data K true 5 a∈pairGroup K g := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α:=Kˣ)
  exact ⟨g,pairGroup_le_canonical K g,pair_recovers_negative_fifth K hcard g hg⟩

end SymmetricSubgroupAsymptotics.CFSGE6GenerationNegativeFifthRecovery
