import SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleElevenPointTitsExclusion
import SymmetricSubgroupAsymptotics.OddBlockOrdinaryGeneratorInduction

/-! Extend the genuine bounded half-degree induction through10. The new
imprimitive local size5 has two blocks and uses actual odd-fibre rounding.
Primitive Tits actions are excluded by the proved512 order divisor. A
failure retains the precise minimal primitive sporadic action; this witness
is global, not asserted to be a subquotient of the original input group.
No new model-order/generator hypothesis or global permutation bound occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TenPointHalfDegreeFiniteModelReduction
open PrimitiveSocleRawStructure PermutationOrdinarySmallerActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open EightPointHalfDegreeFiniteModelReduction

private theorem half_degree_of_imprimitive_small (n : ℕ) (hn : 4 ≤ n) (hsmall : n ≤ 10)
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
  have hr5 : Nat.card block.Fibre ≤ 5 := by nlinarith only [hprod,htop,hsmall]
  have hcases : Nat.card block.Fibre = 2 ∨ Nat.card block.Fibre = 3 ∨
      Nat.card block.Fibre = 4 ∨ Nat.card block.Fibre = 5 := by omega
  have hrel : Nat.card block.Fibre = (MulAction.stabilizer J x).relIndex block.subgroup :=
    originalTransitiveBlockFibre_card x block.subgroup block.covers.le
  rcases hcases with h2 | h3 | h4 | h5
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
  · have hb : SmallerActionBound (Nat.card (Fin n)) := by
      simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
    have hthree : Nat.card block.Points ≠ 3 := by rw [h5] at hprod; omega
    have hh := OddBlockOrdinaryGeneratorInduction.half_degree_of_odd_fibres
      block.map block.map_equivariant block.base (by rw [h5]; decide)
      (by change 5 ≤ Nat.card block.Fibre; omega) block.degrees_ge_two.2 hthree hb
    simpa only [Nat.card_fin] using hh

theorem exists_minimal_primitive_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : n ≤ 10)
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
  have hm10 : m ≤ 10 := hmn.trans hn
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
    have hhalf := half_degree_of_imprimitive_small m hm4 hm10 K ht hh hbelow
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
      exact (PrimitiveSocleElevenPointTitsExclusion.not_tits_of_degree_le_eleven D
        (by simpa only [Nat.card_fin] using (show m ≤ 11 by omega)) e).elim
    case sporadic s =>
      exact ⟨⟨m,hm4,hmn,K,ht,hp,hKbad,hmin,D,s,e⟩⟩

theorem half_degree_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : n ≤ 10)
    (J : Subgroup (Equiv.Perm (Fin n))) (hthree : n = 3 → J ≠ ⊤) :
    2*MarkedC4.genRank J ≤ n ∨ Nonempty (PrimitiveSporadicCounterexample n) := by
  by_cases hh : 2*MarkedC4.genRank J ≤ n
  · exact Or.inl hh
  · exact Or.inr (exists_minimal_primitive_sporadic_counterexample hCFSG n hn J hthree
      (lt_of_not_ge hh))

theorem two_mul_genRank_le_card_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) {G X : Type}
    [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (hsmall : Nat.card X ≤ 10) (hthree : Nat.card X ≠ 3) :
    2*MarkedC4.genRank G ≤ Nat.card X ∨
      Nonempty (PrimitiveSporadicCounterexample 10) := by
  let e : X ≃ Fin (Nat.card X) := Finite.equivFinOfCardEq rfl
  let rho : G →* Equiv.Perm (Fin (Nat.card X)) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have hrho : Function.Injective rho :=
    e.permCongrHom.injective.comp MulAction.toPerm_injective
  let f : G ≃* rho.range := MonoidHom.ofInjective hrho
  rcases half_degree_or_sporadic_counterexample hCFSG (Nat.card X) hsmall
    rho.range (fun h => (hthree h).elim) with hpaid | hbad
  · exact Or.inl (by
      simpa only [← CoprimeNilpotentProductGenerators.genRank_mulEquiv f] using hpaid)
  · exact Or.inr (EightPointFaithfulActionHalfDegreeReduction.counterexample_mono hsmall hbad)

end SymmetricSubgroupAsymptotics.TenPointHalfDegreeFiniteModelReduction
