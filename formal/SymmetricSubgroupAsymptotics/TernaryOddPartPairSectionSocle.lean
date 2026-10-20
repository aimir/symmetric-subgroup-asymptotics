import SymmetricSubgroupAsymptotics.ElementaryKernelTwoChartSchurCapacity
import SymmetricSubgroupAsymptotics.BinaryBySymmetricThreeSocle
import SymmetricSubgroupAsymptotics.BinaryPairResidualTop

/-!
# Four socle generators from the actual pair-module degree-two bound

The selected binary socle is an elementary section of the original group.
Filtering it by the actual pair kernel retains its literal conjugation
action. Only its scalar degree-two constituents use the pair certificate;
the other types use sectional rank twelve. The odd socle shares the same
four slots for a solvable group with at most one factor of three.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem binarySocle_normalGen_le_four_of_pairSection
    {Q B : Type} [Group Q] [Finite Q] [Group B] [Finite B]
    (pi : Q →* B) {K : Rep (ZMod 2) B} [Finite K]
    (F : OriginalKernelModuleChart pi K)
    (hsection : PrimeSectionalRankBound 2 Q 12)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 4)
    (hcard : Nat.card B ∣ 48)
    (hpair : ∀ {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W] (sigma : Representation (ZMod 2) Q W),
      [IsSimpleModule (ZMod 2)[Q] sigma.asModule] →
      Module.finrank (ZMod 2) W = 2 →
      Module.finrank (ZMod 2) (Module.End (ZMod 2)[Q] sigma.asModule) = 2 →
      schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[Q])
        (A := (inflatedRepresentation pi K.ρ).asModule) (X := sigma.asModule) ≤ 2) :
    MarkedC4.normalGen (minimalNormalSoclePart Q (fun M ↦ IsPGroup 2 M)) ≤ 4 := by
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
      selectedPrimeSoclePart_quotientRepresentation_isSemisimple 2 (G := Q) (fun _ ↦ True)
  let f : Multiplicative C.V →* Q := E.subtype.comp C.equiv.symm.toMonoidHom
  have hf : Function.Injective f := E.subtype_injective.comp C.equiv.symm.injective
  have hdim : Module.finrank (ZMod 2) C.V ≤ 12 := by
    have h := primeCharacterRank_le_of_injective 2 hsection f hf
    change binaryCharacterRank (Multiplicative C.V) ≤ 12 at h
    rwa [binaryCharacterRank_multiplicative] at h
  have hfixed : Module.finrank (ZMod 2) sigma.invariants ≤ 4 :=
    (C.originalKernelChart.invariants_finrank_le_centralOmega
      (QuotientGroup.mk'_surjective E)).trans hcentral
  have hfixedComp : Module.finrank (ZMod 2)
      (inflatedRepresentation (QuotientGroup.mk' E) sigma).invariants ≤ 4 := by
    rw [representation_invariants_comp_onto sigma
      (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)]
    exact hfixed
  have hcapacity := C.originalKernelChart.schurCapacity_le_four_of_two_charts
    pi F hdim hfixedComp hcard hpair
  rw [representationSchurCapacity_comp (QuotientGroup.mk' E)
    (QuotientGroup.mk'_surjective E)] at hcapacity
  have hgen : RepresentationGeneratedBy sigma 4 :=
    semisimple_representationGeneratedBy_of_schurCapacity_le sigma 4 hcapacity
  have hnormal : MarkedC4.normalGen E ≤ 4 :=
    normalGen_le_of_elementaryQuotientRepresentation_generated E C 4 hgen
  simpa only [E, true_and] using hnormal

theorem socleNormalGeneratorBound_four_of_isSolvable_pairSection
    {Q B : Type} [Group Q] [Finite Q] [IsSolvable Q] [Group B] [Finite B]
    (pi : Q →* B) {K : Rep (ZMod 2) B} [Finite K]
    (F : OriginalKernelModuleChart pi K)
    (hsection : PrimeSectionalRankBound 2 Q 12)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 4)
    (hcardB : Nat.card B ∣ 48)
    (hpair : ∀ {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W] (sigma : Representation (ZMod 2) Q W),
      [IsSimpleModule (ZMod 2)[Q] sigma.asModule] →
      Module.finrank (ZMod 2) W = 2 →
      Module.finrank (ZMod 2) (Module.End (ZMod 2)[Q] sigma.asModule) = 2 →
      schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[Q])
        (A := (inflatedRepresentation pi K.ρ).asModule) (X := sigma.asModule) ≤ 2)
    {a : ℕ} (hcardQ : Nat.card Q ∣ 2 ^ a * 3) :
    SocleNormalGeneratorBound Q 4 := by
  have hbinary := binarySocle_normalGen_le_four_of_pairSection
    pi F hsection hcentral hcardB hpair
  have hodd := nonbinarySocle_normalGen_le_one_of_isSolvable_ternaryOddPart hcardQ
  apply (socleNormalGeneratorBound_iff_normalGen_le Q 4).2
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts 2 Q).trans
    (max_le hbinary (hodd.trans (by decide)))

end SymmetricSubgroupAsymptotics

end
