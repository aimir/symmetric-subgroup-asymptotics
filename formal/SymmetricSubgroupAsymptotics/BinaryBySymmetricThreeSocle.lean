import SymmetricSubgroupAsymptotics.NoTernaryQuotientSchurCapacity
import SymmetricSubgroupAsymptotics.PrimeSocleSemisimple
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators
import SymmetricSubgroupAsymptotics.SemisimpleModuleGenerators
import SymmetricSubgroupAsymptotics.OriginalKernelCenter
import SymmetricSubgroupAsymptotics.BinaryCharacterProducts
import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank
import SymmetricSubgroupAsymptotics.TernaryOddPartRelativeAnchor

/-!
# Four socle generators for binary extensions of `S₃`

The binary socle itself is an actual elementary section of the original
group. Its dimension is bounded by twelve through permutation sectional
rank, and its fixed vectors inject into the original central binary omega.
The absence of an order-three quotient bounds every nonfixed Schur row by
four. Semisimplicity and the elementary chart produce four ambient normal
generators. The nonbinary socle has order at most three and shares those
slots by the proved prime-type sharing theorem.

The final theorem keeps an actual surjection from the faithful 24-point
group, an actual binary-kernel `S₃` quotient of that original group, and
the central-rank-four and odd-part hypotheses on the retained quotient.
No literal exceptional row certificate is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Fixed vectors of any actual elementary binary kernel embed into
the central binary omega of the ambient group. Faithfulness of the
quotient action is not needed for this direction. -/
theorem OriginalKernelModuleChart.invariants_finrank_le_centralOmega
    {Q B : Type} [Group Q] [Finite Q] [Group B]
    {pi : Q →* B} {A : Rep (ZMod 2) B} [Finite A]
    (E : OriginalKernelModuleChart pi A) (hpi : Function.Surjective pi) :
    Module.finrank (ZMod 2) A.ρ.invariants ≤
      Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) := by
  let f : A.ρ.invariants → binaryCentralOmega Q := fun a ↦
    ⟨⟨E.element a, (E.element_mem_center_iff hpi a).mpr a.property⟩,
      Subtype.ext (E.element_sq a)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply E.element_injective
    exact congrArg (fun z : binaryCentralOmega Q ↦ binaryCentralOmegaEmbedding z) hab
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  calc
    2 ^ Module.finrank (ZMod 2) A.ρ.invariants = Nat.card A.ρ.invariants := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ ≤ Nat.card (binaryCentralOmega Q) := Nat.card_le_card_of_injective f hf
    _ = Nat.card (Additive (binaryCentralOmega Q)) :=
      Nat.card_congr (Additive.toMul : Additive (binaryCentralOmega Q) ≃
        binaryCentralOmega Q).symm
    _ = 2 ^ Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- Any elementary binary subgroup of an actual quotient is controlled
by the original permutation action's sectional rank. -/
theorem binarySectionalRankBound_of_faithful_permutation_quotient
    {G Q X : Type} [Group G] [Finite G] [Group Q]
    [Finite X] [MulAction G X] [FaithfulSMul G X]
    (pi : G →* Q) (hpi : Function.Surjective pi) :
    PrimeSectionalRankBound 2 Q (Nat.card X / 2) := by
  have hG : PrimeSectionalRankBound 2 G (Nat.card X / 2) := by
    intro L
    exact permutation_primeCharacterRank_le 2 L X
  intro L
  exact PrimeSectionalRankBound.quotient_rank_le 2 hG (L.comap pi)
    (pi.subgroupComap L) (pi.subgroupComap_surjective_of_surjective L hpi)

/-- The whole binary socle needs four ambient normal generators from
actual elementary-section rank twelve, actual central rank four, and no
order-three quotient. Its selected-prime chart supplies semisimplicity. -/
theorem binarySocle_normalGen_le_four_of_noTernaryQuotient
    {Q : Type} [Group Q] [Finite Q]
    (hno : NoTernaryQuotient Q)
    (hsection : PrimeSectionalRankBound 2 Q 12)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 4) :
    MarkedC4.normalGen
      (minimalNormalSoclePart Q (fun M ↦ IsPGroup 2 M)) ≤ 4 := by
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
  have hdim : Module.finrank (ZMod 2) C.V ≤ 12 := by
    have h := primeCharacterRank_le_of_injective 2 hsection f hf
    change binaryCharacterRank (Multiplicative C.V) ≤ 12 at h
    rwa [binaryCharacterRank_multiplicative] at h
  have hfixed : Module.finrank (ZMod 2) sigma.invariants ≤ 4 :=
    (C.originalKernelChart.invariants_finrank_le_centralOmega
      (QuotientGroup.mk'_surjective E)).trans hcentral
  have hnoQuotient : NoTernaryQuotient (Q ⧸ E) :=
    hno.of_surjective (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
  have hgen : RepresentationGeneratedBy sigma 4 :=
    semisimple_representationGeneratedBy_of_schurCapacity_le sigma 4
      (representationSchurCapacity_le_four_of_noTernaryQuotient
        hnoQuotient sigma hdim hfixed)
  have hnormal : MarkedC4.normalGen E ≤ 4 :=
    normalGen_le_of_elementaryQuotientRepresentation_generated E C 4 hgen
  simpa only [E, true_and] using hnormal

/-- Four generators for the whole literal socle, under the inherited
solvability and order-three quotient obstruction. The odd socle shares
the binary slots. -/
theorem socleNormalGeneratorBound_four_of_isSolvable_noTernaryQuotient
    {Q : Type} [Group Q] [Finite Q] [IsSolvable Q] {a : ℕ}
    (hno : NoTernaryQuotient Q)
    (hsection : PrimeSectionalRankBound 2 Q 12)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 4)
    (hcard : Nat.card Q ∣ 2 ^ a * 3) :
    SocleNormalGeneratorBound Q 4 := by
  have hbinary := binarySocle_normalGen_le_four_of_noTernaryQuotient
    hno hsection hcentral
  have hodd := nonbinarySocle_normalGen_le_one_of_isSolvable_ternaryOddPart hcard
  apply (socleNormalGeneratorBound_iff_normalGen_le Q 4).2
  exact (normalGen_finiteGroupSocle_le_max_primePrimaryParts 2 Q).trans
    (max_le hbinary (hodd.trans (by decide)))

/-- A displayed binary-kernel `S₃` quotient discharges both structural
conditions in the whole-socle theorem. -/
theorem socleNormalGeneratorBound_four_of_binary_kernel_symmetricThree
    {Q : Type} [Group Q] [Finite Q] {a : ℕ}
    (beta : Q →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker)
    (hsection : PrimeSectionalRankBound 2 Q 12)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 4)
    (hcard : Nat.card Q ∣ 2 ^ a * 3) :
    SocleNormalGeneratorBound Q 4 := by
  letI : IsSolvable Q := isSolvable_of_binary_kernel_symmetricThree beta hker
  exact socleNormalGeneratorBound_four_of_isSolvable_noTernaryQuotient
    (noTernaryQuotient_of_binary_kernel_symmetricThree beta hbeta hker)
    hsection hcentral hcard

/-- The original faithful 24-point action discharges the elementary
section bound for every displayed quotient. The other hypotheses concern
that actual quotient and its actual `S₃` reduction. -/
theorem socleNormalGeneratorBound_four_of_twentyFour_binary_kernel_symmetricThree
    {G Q X : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    [Finite X] [MulAction G X] [FaithfulSMul G X] {a : ℕ}
    (pi : G →* Q) (hpi : Function.Surjective pi) (hX : Nat.card X = 24)
    (beta : Q →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 4)
    (hcard : Nat.card Q ∣ 2 ^ a * 3) :
    SocleNormalGeneratorBound Q 4 := by
  have hsection := binarySectionalRankBound_of_faithful_permutation_quotient
    (X := X) pi hpi
  rw [hX] at hsection
  exact socleNormalGeneratorBound_four_of_binary_kernel_symmetricThree
    beta hbeta hker hsection hcentral hcard

/-- The `S₃` map is needed only on the original 24-point group. Both
solvability and the absence of a ternary quotient descend along `pi`;
no new `S₃` quotient is chosen on the retained group. -/
theorem socleNormalGeneratorBound_four_of_original_binary_kernel_symmetricThree
    {G Q X : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    [Finite X] [MulAction G X] [FaithfulSMul G X] {a : ℕ}
    (pi : G →* Q) (hpi : Function.Surjective pi) (hX : Nat.card X = 24)
    (beta : G →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 4)
    (hcard : Nat.card Q ∣ 2 ^ a * 3) :
    SocleNormalGeneratorBound Q 4 := by
  letI : IsSolvable G := isSolvable_of_binary_kernel_symmetricThree beta hker
  letI : IsSolvable Q := solvable_of_surjective hpi
  have hno : NoTernaryQuotient Q :=
    (noTernaryQuotient_of_binary_kernel_symmetricThree beta hbeta hker).of_surjective
      pi hpi
  have hsection := binarySectionalRankBound_of_faithful_permutation_quotient
    (X := X) pi hpi
  rw [hX] at hsection
  exact socleNormalGeneratorBound_four_of_isSolvable_noTernaryQuotient
    hno hsection hcentral hcard

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- The published whole-socle input and the proved ternary anchor turn
these four normal generators into one ordinary plus three relative slots. -/
noncomputable def ordinaryRelativeAnchor_of_twentyFour_binary_kernel_symmetricThree
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G Q X : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    [Finite X] [MulAction G X] [FaithfulSMul G X] {a : ℕ}
    (pi : G →* Q) (hpi : Function.Surjective pi) (hX : Nat.card X = 24)
    (beta : Q →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 4)
    (hcard : Nat.card Q = 2 ^ a * 3) :
    DegreeTwoPairRelativeKernelAnchor Q (degreeTwoPairOrdinaryRelativeProfile 1 3) :=
  DegreeTwoPairRelativeKernelAnchor.ofTernaryOddPartSocleGeneratorBound hZmud hcard
    (socleNormalGeneratorBound_four_of_twentyFour_binary_kernel_symmetricThree
      pi hpi hX beta hbeta hker hcentral (by rw [hcard]))

/-- Original-group form of the ternary anchor. The only retained group
data are its actual quotient map, central rank and exact odd part. -/
noncomputable def ordinaryRelativeAnchor_of_original_binary_kernel_symmetricThree
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G Q X : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    [Finite X] [MulAction G X] [FaithfulSMul G X] {a : ℕ}
    (pi : G →* Q) (hpi : Function.Surjective pi) (hX : Nat.card X = 24)
    (beta : G →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 4)
    (hcard : Nat.card Q = 2 ^ a * 3) :
    DegreeTwoPairRelativeKernelAnchor Q (degreeTwoPairOrdinaryRelativeProfile 1 3) :=
  DegreeTwoPairRelativeKernelAnchor.ofTernaryOddPartSocleGeneratorBound hZmud hcard
    (socleNormalGeneratorBound_four_of_original_binary_kernel_symmetricThree
      pi hpi hX beta hbeta hker hcentral (by rw [hcard]))

end SymmetricSubgroupAsymptotics

end
