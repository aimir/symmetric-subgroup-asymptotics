import SymmetricSubgroupAsymptotics.OddAffinePairQuotientOrdinaryRank
import SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction
import SymmetricSubgroupAsymptotics.OriginalTernaryBoundedSharpStep

/-! The only bounded imprimitive nine-point affine component has two
blocks. Its actual inverse-pair quotient acts faithfully on at most eight
points, while the same two actual abelian kernels cost three generators.
The precise sporadic failed-action alternative is retained; it is not a
claimed inherited subquotient. No global smaller-action input is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalAffineNineBoundedSharpStep
open OddPrimePowerAffineBlockCoordinates OddPrimePowerAffineBlockPairCompression
open EightPointHalfDegreeFiniteModelReduction TraceySharpHalfDegreeNumerics

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.1; omega)
local instance pointsNontrivial : Nontrivial block.Points :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.2; omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

include P in
theorem genRank_le_sharpFloor_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hr : Nat.card block.Fibre = 9) (hsmall : n < 22) :
    MarkedC4.genRank J ≤ sharpFloor n ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  let b := block.map
  let hb := block.map_equivariant
  let C := P.elementaryChart block.component_preprimitive
  let origin : block.Fibre := ⟨x₀,block.map_base⟩
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_equiv P.V
    (C.equiv.toEquiv.trans (Multiplicative.toAdd : Multiplicative C.V ≃ C.V))
  have hproduct : 9*Nat.card block.Points = n := by
    simpa only [hr,Nat.card_fin] using block.degree_product
  have ht : Nat.card block.Points = 2 := by
    have hh := block.degrees_ge_two.2
    omega
  have hn : n = 18 := by omega
  have hpow : P.p^C.d = 9 := by
    have he := P.degree_eq_prime_pow_finrank C.equiv origin
    simpa only [PrimitiveAffineProfile.ElementaryChart.d,hr] using he.symm
  have hpdiv : P.p ∣ 3^2 := by
    change P.p ∣ 9
    rw [← hpow]
    exact dvd_pow_self _ C.d_pos.ne'
  have hp : P.p = 3 := Nat.prime_eq_prime_of_dvd_pow P.p_prime (by decide) hpdiv
  have hd : C.d = 2 := Nat.pow_right_injective (by decide : 2 ≤ 3)
    (by simpa only [hp] using hpow)
  have hfree : ∀ v : Multiplicative C.V, v ≠ 1 → v⁻¹ ≠ v := by
    intro v hv he
    have hnv : C.equiv.symm v ≠ 1 := by
      intro h
      apply hv
      simpa only [C.equiv.apply_symm_apply,map_one] using congrArg C.equiv h
    have he' : (C.equiv.symm v)⁻¹ = C.equiv.symm v :=
      (map_inv C.equiv.symm v).symm.trans (congrArg C.equiv.symm he)
    exact PrimitiveAffineOddOrdinaryInduction.translation_inverse_ne_self P (by omega) _ hnv he'
  have hcard : Nat.card (Multiplicative C.V) = 9 :=
    (Nat.card_congr C.equiv).symm.trans ((P.card_eq origin).trans hr)
  have hpairs : 2*Nat.card (Pairs b hb block.base P block.component_preprimitive C) ≤ 8 := by
    have hh := AbelianAutomorphismInversionPairs.two_mul_pairCard_le (V := Multiplicative C.V) hfree
    simpa only [hcard] using hh
  obtain ⟨v,hv⟩ := exists_ne (1 : Multiplicative C.V)
  letI : Nonempty (Pairs b hb block.base P block.component_preprimitive C) :=
    ⟨FreeInvolutionPairQuotient.mk
      (AbelianAutomorphismInversionPairs.inversion (Multiplicative C.V))
      (AbelianAutomorphismInversionPairs.inversion_involutive (Multiplicative C.V)) ⟨v,hv⟩⟩
  let E := pairKernel b hb block.base P block.component_preprimitive C origin
  let Y := Pairs b hb block.base P block.component_preprimitive C × block.Points
  have hY : Nat.card Y ≤ 8 := by
    change Nat.card (Pairs b hb block.base P block.component_preprimitive C × block.Points) ≤ 8
    rw [Nat.card_prod,ht]
    omega
  have hthree : Nat.card Y ≠ 3 := by
    change Nat.card (Pairs b hb block.base P block.component_preprimitive C × block.Points) ≠ 3
    rw [Nat.card_prod,ht]
    omega
  letI : MulAction (LinearQuotient b hb block.base P origin ⧸ E) Y :=
    MulAction.compHom Y (quotientAction b hb block.base P block.component_preprimitive C origin)
  letI : FaithfulSMul (LinearQuotient b hb block.base P origin ⧸ E) Y := by
    constructor
    intro u w he
    apply quotientAction_injective b hb block.base P block.component_preprimitive C origin
    exact Equiv.ext he
  rcases EightPointFaithfulActionHalfDegreeReduction.two_mul_genRank_le_card_or_sporadic_counterexample
    hCFSG (G := LinearQuotient b hb block.base P origin ⧸ E) (X := Y) hY hthree with hpaid | hbad
  · have hquot : MarkedC4.genRank (LinearQuotient b hb block.base P origin ⧸ E) ≤ 4 := by omega
    have hgen := OddAffinePairQuotientOrdinaryRank.genRank_le_pairQuotient_add_dimension_mul_half
      b hb block.base P block.component_preprimitive C origin
    change MarkedC4.genRank J ≤
      MarkedC4.genRank (LinearQuotient b hb block.base P origin ⧸ E) + (C.d+1)*(Nat.card block.Points/2) at hgen
    have hg : MarkedC4.genRank J ≤ 7 := by rw [hd,ht] at hgen; omega
    exact Or.inl (hg.trans (by simpa only [hn] using
      OriginalTernaryBoundedSharpStep.seven_le_sharpFloor_eighteen))
  · exact Or.inr hbad

include P in
theorem exists_generating_finset_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hr : Nat.card block.Fibre = 9) (hsmall : n < 22) :
    (∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ S.card ≤ sharpFloor n) ∨
      Nonempty (PrimitiveSporadicCounterexample 8) := by
  rcases genRank_le_sharpFloor_or_sporadic_counterexample J block P hCFSG hr hsmall with hpaid | hbad
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨S,hgen,hcard.le.trans hpaid⟩
  · exact Or.inr hbad

end SymmetricSubgroupAsymptotics.OriginalAffineNineBoundedSharpStep
