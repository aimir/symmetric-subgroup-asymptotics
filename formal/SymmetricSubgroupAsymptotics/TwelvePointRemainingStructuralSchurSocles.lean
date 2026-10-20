import SymmetricSubgroupAsymptotics.BinaryBySymmetricThreeSocle

/-! Two shared Schur slots in original twelve-point quotients.
Nonfixed binary simple types use product degree at least three when an
actual order-three quotient is excluded. A six-dimensional elementary
section therefore needs two slots, shared with the actual central type.
These generic structural lemmas do not assert a literal-row certificate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural

local instance remainingStructural_binaryPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {B A : Type} [Group B] [Finite B]
  [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- One nonfixed simple type uses at most two Schur generator positions
inside a binary target of dimension at most six. -/
theorem schurSimpleRatio_le_two_of_noTernaryQuotient
    (hB : NoTernaryQuotient B)
    (sigma : Representation (ZMod 2) B A)
    (hdim : Module.finrank (ZMod 2) A ≤ 6)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    (Module.finrank (ZMod 2) (S →ₗ[(ZMod 2)[B]] sigma.asModule) : ℝ) /
      Module.finrank (ZMod 2) S ≤ 2 := by
  letI : FiniteDimensional (ZMod 2) S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  let q := schurSimpleProductDegree sigma S
  let density : ℝ :=
    (Module.finrank (ZMod 2) (S →ₗ[(ZMod 2)[B]] sigma.asModule) : ℝ) /
      Module.finrank (ZMod 2) S
  have hq : (3 : ℝ) ≤ q := by
    exact_mod_cast three_le_schurSimpleProductDegree_of_noTernaryQuotient
      hB sigma S hnonfixed
  have hnonneg : 0 ≤ density := schurSimpleRatio_nonneg sigma S
  have hoccupied : Module.finrank (ZMod 2) S *
      schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[B])
        (A := sigma.asModule) (X := S) ≤ 6 :=
    (finrank_mul_schurSocleMultiplicity_le
      (k := ZMod 2) (R := (ZMod 2)[B]) (A := sigma.asModule) (X := S)).trans
      (by rw [sigma.asModuleEquiv.finrank_eq]; exact hdim)
  have hproduct : (q : ℝ) * density ≤ 6 := by
    change (schurSimpleProductDegree sigma S : ℝ) *
      ((Module.finrank (ZMod 2) (S →ₗ[(ZMod 2)[B]] sigma.asModule) : ℝ) /
        Module.finrank (ZMod 2) S) ≤ 6
    rw [schurSimpleProductDegree_mul_ratio sigma S 0]
    simp only [schurMixedSocleDimension, zero_add, Nat.cast_zero, sub_zero]
    exact_mod_cast hoccupied
  change density ≤ 2
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) hnonneg]

/-- The fixed and nonfixed rows share two generator positions. The
fixed-rank premise refers to the literal invariant subspace. -/
theorem representationSchurCapacity_le_two_of_noTernaryQuotient
    (hB : NoTernaryQuotient B)
    (sigma : Representation (ZMod 2) B A)
    (hdim : Module.finrank (ZMod 2) A ≤ 6)
    (hfixed : Module.finrank (ZMod 2) sigma.invariants ≤ 2) :
    representationSchurCapacity sigma ≤ 2 := by
  apply (representationSchurCapacity_le_max_fixed_nontrivial sigma 2 ?_).trans
    (max_le (by exact_mod_cast hfixed) le_rfl)
  intro S hS hnonfixed
  letI : IsSimpleModule (ZMod 2)[B] S := hS
  exact schurSimpleRatio_le_two_of_noTernaryQuotient hB sigma hdim S hnonfixed

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural

namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural

/-- The whole binary socle needs two ambient normal generators from
actual elementary-section rank six, actual central rank two, and no
order-three quotient. Its selected-prime chart supplies semisimplicity. -/
theorem binarySocle_normalGen_le_two_of_noTernaryQuotient
    {Q : Type} [Group Q] [Finite Q]
    (hno : NoTernaryQuotient Q)
    (hsection : PrimeSectionalRankBound 2 Q 6)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 2) :
    MarkedC4.normalGen
      (minimalNormalSoclePart Q (fun M ↦ IsPGroup 2 M)) ≤ 2 := by
  let E := minimalNormalSoclePart Q (fun M ↦ True ∧ IsPGroup 2 M)
  let C := selectedPrimeSoclePartElementaryChart 2 (G := Q) (fun _ ↦ True)
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod 2) C.V := C.module
  letI : FiniteDimensional (ZMod 2) C.V := C.finiteDimensional
  letI : FiniteDimensional (ZMod C.p) C.quotientRepresentation := C.finiteDimensional
  letI : Finite C.quotientRepresentation := Module.finite_of_finite (ZMod C.p)
  let sigma : Representation (ZMod 2) (Q ⧸ E) C.V := C.quotientRepresentation.ρ
  letI : Finite C.V := Module.finite_of_finite (ZMod 2)
  letI : IsSemisimpleModule (ZMod 2)[Q ⧸ E] sigma.asModule := by
    simpa only [E, C, sigma] using
      selectedPrimeSoclePart_quotientRepresentation_isSemisimple
        2 (G := Q) (fun _ ↦ True)
  let f : Multiplicative C.V →* Q := E.subtype.comp C.equiv.symm.toMonoidHom
  have hf : Function.Injective f :=
    E.subtype_injective.comp C.equiv.symm.injective
  have hdim : Module.finrank (ZMod 2) C.V ≤ 6 := by
    have h := primeCharacterRank_le_of_injective 2 hsection f hf
    change binaryCharacterRank (Multiplicative C.V) ≤ 6 at h
    rwa [binaryCharacterRank_multiplicative] at h
  have hfixed : Module.finrank (ZMod 2) sigma.invariants ≤ 2 :=
    (C.originalKernelChart.invariants_finrank_le_centralOmega
      (QuotientGroup.mk'_surjective E)).trans hcentral
  have hnoQuotient : NoTernaryQuotient (Q ⧸ E) :=
    hno.of_surjective (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
  have hgen : RepresentationGeneratedBy sigma 2 :=
    semisimple_representationGeneratedBy_of_schurCapacity_le sigma 2
      (representationSchurCapacity_le_two_of_noTernaryQuotient
        hnoQuotient sigma hdim hfixed)
  have hnormal : MarkedC4.normalGen E ≤ 2 :=
    normalGen_le_of_elementaryQuotientRepresentation_generated E C 2 hgen
  simpa only [E, true_and] using hnormal

/-- Two generators for the whole literal socle, under the inherited
solvability and order-three quotient obstruction. The odd socle shares
the binary slots. -/
theorem socleNormalGeneratorBound_two_of_isSolvable_noTernaryQuotient
    {Q : Type} [Group Q] [Finite Q] [IsSolvable Q] {a : ℕ}
    (hno : NoTernaryQuotient Q)
    (hsection : PrimeSectionalRankBound 2 Q 6)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 2)
    (hcard : Nat.card Q ∣ 2 ^ a * 3) :
    SocleNormalGeneratorBound Q 2 := by
  have hbinary := binarySocle_normalGen_le_two_of_noTernaryQuotient
    hno hsection hcentral
  have hodd := nonbinarySocle_normalGen_le_one_of_isSolvable_ternaryOddPart hcard
  apply (socleNormalGeneratorBound_iff_normalGen_le Q 2).2
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts 2 Q).trans
    (max_le hbinary (hodd.trans (by decide)))


end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
