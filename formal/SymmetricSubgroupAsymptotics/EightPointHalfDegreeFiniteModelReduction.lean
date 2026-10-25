import SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleEightPointTitsExclusion
import SymmetricSubgroupAsymptotics.IntransitiveOrdinaryGeneratorInduction
import SymmetricSubgroupAsymptotics.BinaryBlockOrdinaryGeneratorInduction
import SymmetricSubgroupAsymptotics.TernaryBlockOrdinaryGeneratorInduction
import SymmetricSubgroupAsymptotics.FourPointBlockOrdinaryGeneratorInduction
import SymmetricSubgroupAsymptotics.PermutationSmallDegreeOrdinaryGenerators
import Mathlib.Data.Nat.Find

/-! Bounded ordinary half-degree induction on ACTUAL actions through
8, with the full S3 exception. Every failed action yields a least-degree
failed primitive action with an actual sporadic socle factor. Tits is
excluded by its proved original order lower bound. The minimal witness
is a global smaller action: it is NOT asserted to be a subquotient of the
original input group. No new finite-model generator hypothesis is used,
and the sporadic disjunction is not an unconditional eight-point bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction
open PrimitiveSocleRawStructure PermutationOrdinarySmallerActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

/-- Exact actual failed action and its induction minimality. The group
is not claimed to be a subquotient of a preceding input group. -/
structure PrimitiveSporadicCounterexample (bound : ℕ) where
  degree : ℕ
  degree_ge_four : 4 ≤ degree
  degree_le : degree ≤ bound
  group : Subgroup (Equiv.Perm (Fin degree))
  transitive : MulAction.IsPretransitive group (Fin degree)
  primitive : MulAction.IsPreprimitive group (Fin degree)
  failed : degree < 2*MarkedC4.genRank group
  minimal : ∀ k : ℕ, k < degree → ∀ L : Subgroup (Equiv.Perm (Fin k)),
    (k = 3 → L ≠ ⊤) → 2*MarkedC4.genRank L ≤ k
  socle : NonaffineData group (Fin degree)
  sporadic : CFSG.Sporadic
  equiv : socle.Simple ≃* sporadic.Model

private theorem half_degree_of_imprimitive_small (n : ℕ) (hn : 4 ≤ n) (hsmall : n ≤ 8)
    (J : Subgroup (Equiv.Perm (Fin n))) (ht : MulAction.IsPretransitive J (Fin n))
    (hp : ¬ MulAction.IsPreprimitive J (Fin n))
    (hbelow : ∀ k : ℕ, k < n → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2*S.card ≤ k) :
    2*MarkedC4.genRank J ≤ n := by
  letI : MulAction.IsPretransitive J (Fin n) := ht
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  let x : Fin n := ⟨0,by omega⟩
  obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) x hp
  letI : Fintype block.Points := Fintype.ofFinite _
  have hprod := block.degree_product
  simp only [Nat.card_fin] at hprod
  obtain ⟨hr,htop⟩ := block.degrees_ge_two
  have hr4 : Nat.card block.Fibre ≤ 4 := by nlinarith only [hprod,htop,hsmall]
  have hcases : Nat.card block.Fibre = 2 ∨ Nat.card block.Fibre = 3 ∨
      Nat.card block.Fibre = 4 := by omega
  have hrel : Nat.card block.Fibre = (MulAction.stabilizer J x).relIndex block.subgroup :=
    originalTransitiveBlockFibre_card x block.subgroup block.covers.le
  rcases hcases with h2 | h3 | h4
  · let pair : TransitiveBinaryPairCover J x :=
      ⟨block.subgroup,block.covers,hrel.symm.trans h2⟩
    obtain ⟨S,hgen,hcard⟩ := BinaryBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
      n J ht x pair block.proper hbelow
    exact (Nat.mul_le_mul_left 2 (MarkedC4.genRank_le hgen)).trans hcard
  · obtain ⟨S,hgen,hcard⟩ := TernaryBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
      n J ht x block.subgroup block.covers.le block.proper (hrel.symm.trans h3) hbelow
    exact (Nat.mul_le_mul_left 2 (MarkedC4.genRank_le hgen)).trans hcard
  · obtain ⟨S,hgen,hcard⟩ := FourPointBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
      n J x block h4 hbelow
    exact (Nat.mul_le_mul_left 2 (MarkedC4.genRank_le hgen)).trans hcard

theorem exists_minimal_primitive_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : n ≤ 8)
    (J : Subgroup (Equiv.Perm (Fin n))) (hthree : n = 3 → J ≠ ⊤)
    (hbad : n < 2*MarkedC4.genRank J) :
    Nonempty (PrimitiveSporadicCounterexample n) := by
  let bad : ℕ → Prop := fun k => ∃ L : Subgroup (Equiv.Perm (Fin k)),
    (k = 3 → L ≠ ⊤) ∧ k < 2*MarkedC4.genRank L
  have hex : ∃ k, bad k := ⟨n,J,hthree,hbad⟩
  let m := Nat.find hex
  have hmBad : bad m := Nat.find_spec hex
  obtain ⟨K,hKthree,hKbad⟩ := hmBad
  change m < 2*MarkedC4.genRank K at hKbad
  have hmn : m ≤ n := Nat.find_min' hex ⟨J,hthree,hbad⟩
  have hm8 : m ≤ 8 := hmn.trans hn
  have hmin : ∀ k : ℕ, k < m → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → 2*MarkedC4.genRank L ≤ k := by
    intro k hk L hL
    by_contra hh
    exact Nat.find_min hex hk ⟨L,hL,lt_of_not_ge hh⟩
  have hm4 : 4 ≤ m := by
    by_contra hh
    have hb := PermutationSmallDegreeOrdinaryGenerators.two_mul_genRank_le_degree
      m K (by omega) hKthree
    exact (not_lt_of_ge hb) hKbad
  have hbelow : ∀ k : ℕ, k < m → ∀ L : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → L ≠ ⊤) → ∃ S : Finset L, Subgroup.closure (S : Set L) = ⊤ ∧ 2*S.card ≤ k := by
    intro k hk L hL
    obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := L)
    exact ⟨S,hgen,by rw [hcard]; exact hmin k hk L hL⟩
  have hb : SmallerActionBound (Nat.card (Fin m)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators m hbelow
  have ht : MulAction.IsPretransitive K (Fin m) := by
    by_contra hh
    have hhalf := IntransitiveOrdinaryGeneratorInduction.half_degree_of_intransitive hh hb
    simp only [Nat.card_fin] at hhalf
    exact (not_lt_of_ge hhalf) hKbad
  have hp : MulAction.IsPreprimitive K (Fin m) := by
    by_contra hh
    have hhalf := half_degree_of_imprimitive_small m hm4 hm8 K ht hh hbelow
    exact (not_lt_of_ge hhalf) hKbad
  rcases PrimitiveBoundedSharpCFSGReduction.genRank_le_sharpFloor_or_actual_residual
    hCFSG m hm4 (by omega) K hp with hpaid | haffine | ⟨D,j,hj,⟨e⟩⟩
  · have hh := hpaid.trans (TraceySharpHalfDegreeNumerics.sharpFloor_le_half m hm4)
    have hhalf := (Nat.mul_le_mul_left 2 hh).trans (Nat.mul_div_le m 2)
    exact ((not_lt_of_ge hhalf) hKbad).elim
  · have hh := haffine.1
    omega
  · cases j <;> try exact hj.elim
    case tits =>
      exact (PrimitiveSocleEightPointTitsExclusion.not_tits_of_degree_le_eight D
        (by simpa only [Nat.card_fin] using hm8) e).elim
    case sporadic s =>
      exact ⟨⟨m,hm4,hmn,K,ht,hp,hKbad,hmin,D,s,e⟩⟩

theorem half_degree_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : n ≤ 8)
    (J : Subgroup (Equiv.Perm (Fin n))) (hthree : n = 3 → J ≠ ⊤) :
    2*MarkedC4.genRank J ≤ n ∨ Nonempty (PrimitiveSporadicCounterexample n) := by
  by_cases hh : 2*MarkedC4.genRank J ≤ n
  · exact Or.inl hh
  · exact Or.inr (exists_minimal_primitive_sporadic_counterexample hCFSG n hn J hthree
      (lt_of_not_ge hh))

theorem genRank_le_four_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (J : Subgroup (Equiv.Perm (Fin 8))) :
    MarkedC4.genRank J ≤ 4 ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  rcases half_degree_or_sporadic_counterexample hCFSG 8 (by decide) J (by omega) with hh | hr
  · exact Or.inl (by omega)
  · exact Or.inr hr

end SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction
