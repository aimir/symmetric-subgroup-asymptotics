import SymmetricSubgroupAsymptotics.OriginalBlockOrdinaryCompressionState
import SymmetricSubgroupAsymptotics.ActualWreathChiefOrderDivisibility
import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank

/-! The first characteristic position for an ACTUAL primitive affine
block component is its literal regular translation subgroup. The tail
is the actual quotient by translations, with a proved p^(d^2) order
bound from its faithful linear complement. No composition-length input,
permutation-generator input, or desired aggregate estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineBlockCharacteristicHead
open ActualWreathCharacteristicChiefProfile ActualWreathChiefOrderDivisibility

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

private def origin : block.Fibre := ⟨x₀, block.map_base⟩

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

def translationDimension : ℕ := (P.elementaryChart block.component_preprimitive).d

def translationChart : ElementaryMinimalNormalChart (QuotientGroup.mk' P.V).ker := by
  let C := P.elementaryChart block.component_preprimitive
  exact {
    p := P.p
    p_prime := P.p_prime
    primeFact := C.primeFact
    V := C.V
    addCommGroup := C.addCommGroup
    module := C.module
    finiteDimensional := C.finiteDimensional
    equiv := (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' P.V)).trans C.equiv }

def headCharge (i : block.Points) : ElementaryCharge (Fintype.card block.Points) :=
  actualCharge (OriginalBlockOrdinaryCompressionState.initialState J block)
    (QuotientGroup.mk' P.V) (translationChart J block P) i (by
      simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2)

theorem headCharge_prime (i : block.Points) : (headCharge J block P i).p = P.p := rfl

theorem headCharge_dimension (i : block.Points) :
    (headCharge J block P i).dimension = translationDimension J block P := rfl

omit [Fintype block.Points] in
theorem fibre_card_eq_prime_pow_dimension :
    Nat.card block.Fibre = P.p ^ translationDimension J block P := by
  let C := P.elementaryChart block.component_preprimitive
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  simpa only [translationDimension, PrimitiveAffineProfile.ElementaryChart.d] using
    P.degree_eq_prime_pow_finrank C.equiv (origin J block)

omit [Fintype block.Points] in
theorem translation_kernel_minimal :
    IsMinimalNormalSubgroup (QuotientGroup.mk' P.V).ker := by
  letI : Nontrivial P.V := (P.pointEquiv (origin J block)).symm.injective.nontrivial
  have hne : P.V ≠ ⊥ := P.V.nontrivial_iff_ne_bot.mp inferInstance
  have hm : IsMinimalNormalSubgroup P.V := by
    refine ⟨inferInstance, hne, ?_⟩
    intro K hK hKne hKV
    exact (P.minimal block.component_preprimitive K hK hKV).resolve_left hKne
  simpa only [QuotientGroup.ker_mk'] using hm

omit [Fintype block.Points] in
theorem translation_quotient_card_le :
    Nat.card (block.Component ⧸ P.V) ≤ P.p ^ ((translationDimension J block P) ^ 2) := by
  let C := P.elementaryChart block.component_preprimitive
  let x := origin J block
  let e : (block.Component ⧸ P.V) ≃* P.complement x :=
    (QuotientGroup.quotientMulEquivOfEq (P.complementProjection_ker x).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (P.complementProjection x) (P.complementProjection_surjective x))
  calc
    Nat.card (block.Component ⧸ P.V) = Nat.card (P.complement x) := Nat.card_congr e.toEquiv
    _ ≤ P.p ^ (C.d ^ 2) := P.complement_card_le_prime_pow_dimension_sq
      block.component_preprimitive C x
    _ = P.p ^ ((translationDimension J block P) ^ 2) := rfl

def quotientState : ActualWreathCompressionState block.Top block.Points :=
  (OriginalBlockOrdinaryCompressionState.initialState J block).quotient
    (block.Component ⧸ P.V) (QuotientGroup.mk' P.V) (QuotientGroup.mk'_surjective P.V)

/-- Both the head and tail are actual chief traces on the original
faithful block embedding, with the translation dimension in first place. -/
theorem exists_translation_head_and_tail (i : block.Points) :
    ∃ c : ℕ,
      ActualWreathOrdinaryChiefRecurrence.ChiefCost i (quotientState J block P) c ∧
      Nonempty (DivisibleProfile (Fintype.card block.Points) c
        (Nat.card (block.Component ⧸ P.V))) ∧
      ActualWreathOrdinaryChiefRecurrence.ChiefCost i
        (OriginalBlockOrdinaryCompressionState.initialState J block)
        ((headCharge J block P i).capacity + c) ∧
      MarkedC4.genRank J ≤ (headCharge J block P i).capacity + c +
        MarkedC4.genRank block.Top := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  obtain ⟨c, hc, hprof⟩ := exists_divisible_profile (quotientState J block P) i hI
  have hhead : ActualWreathOrdinaryChiefRecurrence.ChiefCost i
      (OriginalBlockOrdinaryCompressionState.initialState J block)
      ((headCharge J block P i).capacity + c) :=
    .elementary (OriginalBlockOrdinaryCompressionState.initialState J block)
      (block.Component ⧸ P.V) (QuotientGroup.mk' P.V) (QuotientGroup.mk'_surjective P.V)
      (translation_kernel_minimal J block P) (translationChart J block P) c hc
  exact ⟨c, hc, hprof, hhead,
    ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hhead⟩

end SymmetricSubgroupAsymptotics.OriginalAffineBlockCharacteristicHead
