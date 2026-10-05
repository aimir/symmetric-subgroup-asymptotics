import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentSourceAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourRegularTranslationResidual
import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeDegreeSource
import SymmetricSubgroupAsymptotics.SchurPGroupCapacity
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Exact local structure in affine degrees four and five

This module records the finite structural input needed before the actual
block-frame arguments are applied. Every statement is made on the literal
primitive component of the literal minimal block.

* a primitive four-point component is the natural `A4` or `S4` action;
* a primitive affine five-point component has order `5`, `10`, or `20`;
* its point stabilizer and the local quotient in the actual wreath embedding
  are cyclic of order dividing four.

The degree-four recognition is a kernel-checked finite statement about
subgroups of `S4`. It is not a catalogue assumption.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

/-- The prime attached to a degree-four affine profile is two. -/
theorem degreeFour_profilePrime_eq_two
    (hr : Nat.card block.Fibre = 4) : P.p = 2 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree0 : Nat.card block.Fibre = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  have hdegree : 4 = P.p ^ C.d := hr.symm.trans hdegree0
  exact (prime_pow_positive_injective (d := C.d) (e := 2)
    P.p_prime Nat.prime_two C.d_pos (by norm_num)
    (hdegree.symm.trans (by norm_num))).1

include P in
/-- A primitive affine four-point component is not a two-group. Otherwise
its point stabilizer is a two-group acting irreducibly in defining
characteristic, hence trivially; faithfulness would make the stabilizer
trivial and the whole component regular, contradicting primitivity in
composite degree. -/
theorem degreeFour_component_not_isPGroup_two
    (hr : Nat.card block.Fibre = 4) :
    ¬ IsPGroup 2 block.Component := by
  intro htwo
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  let x := origin block
  let rho := (P.complementRepresentation block.component_preprimitive C x).ρ
  have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
  have hcompTwo : IsPGroup 2 (P.complement x) :=
    htwo.to_subgroup (P.complement x)
  have hcompP : IsPGroup P.p (P.complement x) := hp.symm ▸ hcompTwo
  letI : Representation.IsIrreducible rho :=
    P.complementRepresentation_irreducible
      block.component_preprimitive C x
  have htrivial : ∀ g v, rho g v = v :=
    pGroup_simple_representation_trivial hcompP rho
  have hinjective : Function.Injective rho :=
    P.complementRepresentation_injective
      block.component_preprimitive C x
  have hsub : Subsingleton (P.complement x) := ⟨by
    intro a b
    apply hinjective
    apply LinearMap.ext
    intro v
    rw [htrivial a v, htrivial b v]⟩
  letI : Subsingleton (P.complement x) := hsub
  have hcomp : Nat.card (P.complement x) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  have hV : Nat.card P.V = 4 := (P.card_eq x).trans hr
  have hfactor := (P.isComplement'_complement x).card_mul
  rw [hV, hcomp, mul_one] at hfactor
  exact degreeFour_component_card_ne_four block P hr hfactor.symm

include P in
/-- A primitive four-point component has order exactly twelve or
twenty-four. This follows from the exact `GL(2,2)` order divisor, the
literal regular translation subgroup, and the preceding defining-
characteristic exclusion. -/
theorem degreeFour_component_card_eq_twelve_or_twentyFour
    (hr : Nat.card block.Fibre = 4) :
    Nat.card block.Component = 12 ∨ Nat.card block.Component = 24 := by
  have hdiv24 := component_card_dvd_24 block P hr
  have hV : Nat.card P.V = 4 := (P.card_eq (origin block)).trans hr
  have hfactor := (P.isComplement'_complement (origin block)).card_mul
  have hfour : 4 ∣ Nat.card block.Component := by
    refine ⟨Nat.card (P.complement (origin block)), ?_⟩
    exact hfactor.symm.trans (by rw [hV])
  have hle : Nat.card block.Component ≤ 24 :=
    Nat.le_of_dvd (by norm_num) hdiv24
  have hnotTwo := degreeFour_component_not_isPGroup_two block P hr
  obtain ⟨k, hk⟩ := hfour
  have hkpos : 0 < k := by
    have hpos : 0 < Nat.card block.Component := Nat.card_pos
    omega
  have hkle : k ≤ 6 := by omega
  interval_cases k
  · exfalso
    exact degreeFour_component_card_ne_four block P hr (by omega)
  · exfalso
    apply hnotTwo
    apply IsPGroup.of_card (n := 3)
    norm_num at hk ⊢
    exact hk
  · exact Or.inl (by omega)
  · have hcard : Nat.card block.Component = 16 := by omega
    rw [hcard] at hdiv24
    norm_num at hdiv24
  · have hcard : Nat.card block.Component = 20 := by omega
    rw [hcard] at hdiv24
    norm_num at hdiv24
  · exact Or.inr (by omega)

/-- The actual point stabilizer of a degree-four affine component has
order three or six. -/
theorem degreeFour_complement_card_eq_three_or_six
    (hr : Nat.card block.Fibre = 4) :
    Nat.card (P.complement (origin block)) = 3 ∨
      Nat.card (P.complement (origin block)) = 6 := by
  have hV : Nat.card P.V = 4 := (P.card_eq (origin block)).trans hr
  have hfactor := (P.isComplement'_complement (origin block)).card_mul
  rcases degreeFour_component_card_eq_twelve_or_twentyFour block P hr with
    hcomponent | hcomponent
  · left
    rw [hV, hcomponent] at hfactor
    omega
  · right
    rw [hV, hcomponent] at hfactor
    omega

include P in
/-- Exact order divisor for a primitive affine component of degree five. -/
theorem degreeFive_component_card_dvd_twenty
    (hr : Nat.card block.Fibre = 5) :
    Nat.card block.Component ∣ 20 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree0 : Nat.card block.Fibre = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  have hdegree : 5 = P.p ^ C.d := hr.symm.trans hdegree0
  have hp : P.p = 5 := (prime_pow_positive_injective (d := C.d) (e := 1)
    P.p_prime (by norm_num : Nat.Prime 5) C.d_pos (by norm_num)
    (hdegree.symm.trans (by norm_num))).1
  have hdiv := component_card_dvd_degree_mul_GL block P 1 (by
    calc
      Nat.card block.Fibre = 5 := hr
      _ = (5 : ℕ) ^ 1 := by norm_num
      _ = P.p ^ 1 := by rw [hp])
  have hcard : Nat.card
      (Matrix.GeneralLinearGroup (Fin 1) (ZMod P.p)) = 4 := by
    rw [Matrix.card_GL_field, ZMod.card]
    norm_num [hp]
  simpa only [hr, hcard] using hdiv

/-- The literal point stabilizer in degree five has order dividing four. -/
theorem degreeFive_complement_card_dvd_four
    (hr : Nat.card block.Fibre = 5) :
    Nat.card (P.complement (origin block)) ∣ 4 := by
  have hV : Nat.card P.V = 5 := (P.card_eq (origin block)).trans hr
  have hfactor := (P.isComplement'_complement (origin block)).card_mul
  have hdiv := degreeFive_component_card_dvd_twenty block P hr
  rw [hfactor.symm, hV] at hdiv
  apply Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5)
  simpa using hdiv

include P in
/-- A primitive affine five-point component has one of the three possible
orders `5`, `10`, and `20`. -/
theorem degreeFive_component_card_eq_five_or_ten_or_twenty
    (hr : Nat.card block.Fibre = 5) :
    Nat.card block.Component = 5 ∨ Nat.card block.Component = 10 ∨
      Nat.card block.Component = 20 := by
  have hdiv20 := degreeFive_component_card_dvd_twenty block P hr
  have hV : Nat.card P.V = 5 := (P.card_eq (origin block)).trans hr
  have hfactor := (P.isComplement'_complement (origin block)).card_mul
  have hfive : 5 ∣ Nat.card block.Component := by
    refine ⟨Nat.card (P.complement (origin block)), ?_⟩
    calc
      Nat.card block.Component =
          Nat.card P.V * Nat.card (P.complement (origin block)) :=
        hfactor.symm
      _ = 5 * Nat.card (P.complement (origin block)) := by rw [hV]
  have hle : Nat.card block.Component ≤ 20 :=
    Nat.le_of_dvd (by norm_num) hdiv20
  have hpos : 0 < Nat.card block.Component := Nat.card_pos
  have hcases : Nat.card block.Component = 5 ∨
      Nat.card block.Component = 10 ∨ Nat.card block.Component = 15 ∨
      Nat.card block.Component = 20 := by
    obtain ⟨k, hk⟩ := hfive
    omega
  rcases hcases with hcard | hcard | hcard | hcard
  · exact Or.inl hcard
  · exact Or.inr (Or.inl hcard)
  · rw [hcard] at hdiv20
    norm_num at hdiv20
  · exact Or.inr (Or.inr hcard)

/-- The literal translation subgroup in affine degree five has order five. -/
theorem degreeFive_translation_card_eq_five
    (hr : Nat.card block.Fibre = 5) :
    Nat.card P.V = 5 :=
  (P.card_eq (origin block)).trans hr

/-- The affine profile prime is literally five. -/
theorem degreeFive_profilePrime_eq_five
    (hr : Nat.card block.Fibre = 5) : P.p = 5 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  let C := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree0 : Nat.card block.Fibre = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  have hdegree : 5 = P.p ^ C.d := hr.symm.trans hdegree0
  exact (prime_pow_positive_injective (d := C.d) (e := 1)
    P.p_prime (by norm_num : Nat.Prime 5) C.d_pos (by norm_num)
    (hdegree.symm.trans (by norm_num))).1

/-- The literal translation subgroup in affine degree five is cyclic. -/
theorem degreeFive_translation_isCyclic
    (hr : Nat.card block.Fibre = 5) : IsCyclic P.V := by
  have hcard := degreeFive_translation_card_eq_five block P hr
  letI : Fact (Nat.card P.V).Prime := ⟨hcard.symm ▸ by norm_num⟩
  exact isCyclic_of_prime_card rfl

/-- The actual degree-five point stabilizer is cyclic, by its faithful
conjugation action on the literal order-five translation subgroup. -/
theorem degreeFive_complement_isCyclic
    (hr : Nat.card block.Fibre = 5) :
    IsCyclic (P.complement (origin block)) := by
  have hcard := degreeFive_translation_card_eq_five block P hr
  letI : IsCyclic P.V := degreeFive_translation_isCyclic block P hr
  have hUnits : IsCyclic (ZMod (Nat.card P.V))ˣ := by
    rw [hcard]
    exact ZMod.isCyclic_units_prime (by norm_num)
  letI : IsCyclic (ZMod (Nat.card P.V))ˣ := hUnits
  letI : IsCyclic (MulAut P.V) :=
    isCyclic_of_injective (IsCyclic.mulAutMulEquiv P.V).toMonoidHom
      (IsCyclic.mulAutMulEquiv P.V).injective
  exact isCyclic_of_injective (P.complementAction (origin block))
    (P.complementAction_injective (origin block))

/-- The order of the actual cyclic degree-five point stabilizer is one,
two, or four. -/
theorem degreeFive_complement_card_eq_one_or_two_or_four
    (hr : Nat.card block.Fibre = 5) :
    Nat.card (P.complement (origin block)) = 1 ∨
      Nat.card (P.complement (origin block)) = 2 ∨
      Nat.card (P.complement (origin block)) = 4 := by
  have hdiv := degreeFive_complement_card_dvd_four block P hr
  have hle : Nat.card (P.complement (origin block)) ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hdiv
  have hpos : 0 < Nat.card (P.complement (origin block)) := Nat.card_pos
  have hcases : Nat.card (P.complement (origin block)) = 1 ∨
      Nat.card (P.complement (origin block)) = 2 ∨
      Nat.card (P.complement (origin block)) = 3 ∨
      Nat.card (P.complement (origin block)) = 4 := by
    omega
  rcases hcases with hcard | hcard | hcard | hcard
  · exact Or.inl hcard
  · exact Or.inr (Or.inl hcard)
  · rw [hcard] at hdiv
    norm_num at hdiv
  · exact Or.inr (Or.inr hcard)

/-- The exact local quotient in the actual wreath embedding is cyclic. -/
theorem degreeFive_localQuotient_isCyclic
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 5) :
    IsCyclic (LocalQuotient block P) := by
  letI : IsCyclic (P.complement (origin block)) :=
    degreeFive_complement_isCyclic block P hr
  exact isCyclic_of_surjective
    (complementAction block P).rangeRestrict
    (MonoidHom.rangeRestrict_surjective (complementAction block P))

/-- The literal complement and the local quotient are the same group after
faithful range compression. -/
noncomputable def degreeFiveLocalComplementEquiv
    [Nontrivial block.Fibre] :
    P.complement (origin block) ≃* LocalQuotient block P :=
  MulEquiv.ofBijective (complementAction block P).rangeRestrict
    ⟨fun a b h => complementAction_injective block P
        (congrArg Subtype.val h),
      (complementAction block P).rangeRestrict_surjective⟩

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
