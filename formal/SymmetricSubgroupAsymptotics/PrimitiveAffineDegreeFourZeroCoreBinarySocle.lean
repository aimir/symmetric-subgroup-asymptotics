import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreBinaryDimensions
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreBinarySchurThree
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreBinarySchurTwo
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreBinarySchurAssembly
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-!
# Assemble the noncentral binary socle row

For each literal retained quotient, the selected noncentral binary socle is
a semisimple module.  Its translation section, top quotient, and the two
exceptional Schur rows satisfy the exact five-eighths budget.  This file
assembles those inputs, transports a generating tuple back through the
literal elementary chart, and obtains ambient normal generators for the
actual selected socle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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
  [Nontrivial block.Fibre]

/-- The literal selected noncentral binary socle uses the sharp
five-eighths generator budget on the two surviving frames. -/
theorem degreeFourZeroCore_noncentralBinary_normalGen_le_schurSlots
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8 ∨ Nat.card block.Points = 16)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    MarkedC4.normalGen (DegreeFourBinarySocle block P N) ≤
      degreeFourZeroCoreSchurSlots (Nat.card block.Points) := by
  let Q := DegreeFourRetainedQuotient N
  let A := DegreeFourBinarySocle block P N
  let C := DegreeFourBinarySocleChart block P N
  let sigma := C.quotientRepresentation.ρ
  let T := DegreeFourBinaryTargetSection block P N
  have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hCp : C.p = P.p := by
    dsimp only [C, DegreeFourBinarySocleChart,
      selectedPrimeSoclePartElementaryChart]
  have hcard : Nat.card (ZMod C.p) = 2 := by
    rw [Nat.card_zmod, hCp, hp]
  letI : Fact C.p.Prime := C.primeFact
  letI : FiniteDimensional (ZMod C.p) C.quotientRepresentation :=
    C.finiteDimensional
  letI : Module (ZMod C.p)[Q ⧸ A] sigma.asModule :=
    Representation.instModuleMonoidAlgebraAsModule sigma
  letI : IsScalarTower (ZMod C.p) (ZMod C.p)[Q ⧸ A] sigma.asModule :=
    inferInstanceAs
      (IsScalarTower (ZMod C.p) (ZMod C.p)[Q ⧸ A]
        (Representation.asModule sigma))
  let hsemiP : IsSemisimpleModule
      (ZMod P.p)[Q ⧸ A] sigma.asModule := by
    simpa only [Q, A, C, sigma, DegreeFourBinarySocle,
      DegreeFourBinarySocleChart] using
      (selectedPrimeSoclePart_quotientRepresentation_isSemisimple
        P.p (G := DegreeFourRetainedQuotient N)
        (fun M ↦ ¬ M ≤ Subgroup.center (DegreeFourRetainedQuotient N)))
  letI : IsSemisimpleModule (ZMod C.p)[Q ⧸ A] sigma.asModule := by
    simpa only [hCp] using hsemiP
  letI : Module (ZMod C.p) T.toSubmodule := T.toSubmodule.module
  letI : FiniteDimensional (ZMod C.p) T.toSubmodule :=
    FiniteDimensional.finiteDimensional_submodule T.toSubmodule
  letI : FiniteDimensional (ZMod C.p) T.asSubmodule :=
    FiniteDimensional.of_injective
      (T.asSubmodule.subtype.restrictScalars (ZMod C.p))
      T.asSubmodule.subtype_injective
  let hfiniteTargetP : FiniteDimensional (ZMod P.p) T.asSubmodule := by
    simpa only [hCp] using
      (inferInstance : FiniteDimensional (ZMod C.p) T.asSubmodule)
  letI : FiniteDimensional (ZMod P.p) T.asSubmodule := hfiniteTargetP
  letI : FiniteDimensional (ZMod C.p) (sigma.asModule ⧸ T.asSubmodule) :=
    FiniteDimensional.of_surjective
      (T.asSubmodule.mkQ.restrictScalars (ZMod C.p))
      T.asSubmodule.mkQ_surjective
  have hcoinv : Module.finrank (ZMod C.p) sigma.Coinvariants = 0 := by
    simpa only [hCp, C, sigma] using
      (degreeFourBinarySocle_coinvariants_eq_zero block P N)
  have hnonfixed : ∀ S : Submodule (ZMod C.p)[Q ⧸ A] sigma.asModule,
      [IsSimpleModule (ZMod C.p)[Q ⧸ A] S] →
      ¬ representationSubmoduleFixed sigma S := by
    intro S _hS
    exact not_representationSubmoduleFixed_of_semisimple_coinvariants_zero
      sigma hcoinv S
  have htranslation : Module.finrank (ZMod C.p) T.toSubmodule ≤
      2 * Nat.card block.Points :=
    degreeFourBinaryTargetSection_finrank_le_twice_blocks block P hr N
  have htop0 : 2 * Module.finrank (ZMod C.p)
      (sigma.asModule ⧸ T.toSubmodule) ≤ Nat.card block.Points := by
    simpa only [C, sigma, T] using
      degreeFourBinaryTopQuotient_twice_finrank_le_blocks
        block P hr hD N
  have htop : 2 * Module.finrank (ZMod C.p)
      (sigma.asModule ⧸ T.asSubmodule) ≤ Nat.card block.Points := by
    simpa only [Subrepresentation.asSubmodule] using htop0
  have hgen : RepresentationGeneratedBy sigma
      (degreeFourZeroCoreSchurSlots (Nat.card block.Points)) := by
    apply degreeFourZeroCore_semisimple_generated_of_schur_filtration
      hcard sigma T.asSubmodule (Nat.card block.Points) hs hnonfixed
      htranslation htop
    · intro S hsimpleC hS hSE
      letI : IsSimpleModule (ZMod C.p)[Q ⧸ A] S := hsimpleC
      let hsimpleP : IsSimpleModule (ZMod P.p)[Q ⧸ A] S := by
        simpa only [hCp] using hsimpleC
      letI : IsSimpleModule (ZMod P.p)[Q ⧸ A] S := hsimpleP
      simpa only [hCp] using
        (degreeFourBinaryTranslation_schurThree_le_blocks
          block P hTraceyPerm hr hs N S (hnonfixed S) hS hSE)
    · intro S hsimpleC hS hSE
      letI : IsSimpleModule (ZMod C.p)[Q ⧸ A] S := hsimpleC
      let hsimpleP : IsSimpleModule (ZMod P.p)[Q ⧸ A] S := by
        simpa only [hCp] using hsimpleC
      letI : IsSimpleModule (ZMod P.p)[Q ⧸ A] S := hsimpleP
      simpa only [hCp] using
        (degreeFourBinaryTranslation_schurTwo_le_blocks
          block P hTraceyPerm hr hs N S (hnonfixed S) hS hSE)
  let W : Subrepresentation sigma :=
    C.originalKernelChart.normalSubrepresentation
      (QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A)
      C.quotientRepresentation A
  let inclusion : W.toRepresentation.IntertwiningMap sigma := {
    toLinearMap := W.toSubmodule.subtype
    isIntertwining' := by intro _; rfl }
  have hinclusion : Function.Bijective inclusion := by
    constructor
    · exact W.toSubmodule.subtype_injective
    · intro v
      let a : A := C.equiv.symm (Multiplicative.ofAdd v)
      have hva : (C.equiv a).toAdd = v := by
        dsimp only [a]
        rw [C.equiv.apply_symm_apply]
        rfl
      have hvW : v ∈ W := by
        rw [← hva]
        exact (elementaryIntersectionModule_mem_iff A C A a).2 a.2
      exact ⟨⟨v, hvW⟩, rfl⟩
  let e := inclusion.ofBijective hinclusion
  have hgenW : RepresentationGeneratedBy W.toRepresentation
      (degreeFourZeroCoreSchurSlots (Nat.card block.Points)) :=
    representationGeneratedBy_of_surjective sigma W.toRepresentation
      e.symm.toIntertwiningMap e.symm.surjective hgen
  exact normalGen_le_of_elementaryNormalSubrepresentation_generated
    A C A le_rfl (degreeFourZeroCoreSchurSlots (Nat.card block.Points))
    (by simpa only [W] using hgenW)

/-- Exact five-slot noncentral-socle upgrade on the eight-block frame. -/
noncomputable def degreeFourZeroCoreEightNoncentralSocleUpgrade
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    DegreeFourZeroCoreNoncentralSocleUpgrade block P 8 5 := by
  intro hr hD hs hhead N hretained
  let bounds : DegreeFourZeroCoreNoncentralSocleBounds block P 5 :=
    degreeFourZeroCoreNoncentralSocleBounds_of_binary block P hMN hr hD
      (by omega) (by
        rw [hs]
        norm_num [degreeFourSocleSlots]) (by
          intro K _hK
          have hbinary :=
            degreeFourZeroCore_noncentralBinary_normalGen_le_schurSlots
              block P hTraceyPerm hr hD (Or.inl hs) K
          have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
          simpa only [DegreeFourBinarySocle, hp, hs,
            degreeFourZeroCoreSchurSlots] using hbinary)
  exact (degreeFourZeroCoreNoncentralSocleUpgrade_of_bounds
    (framePoints := 8) block P bounds) hr hD hs hhead N hretained

/-- Exact ten-slot noncentral-socle upgrade on the sixteen-block frame. -/
noncomputable def degreeFourZeroCoreSixteenNoncentralSocleUpgrade
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    DegreeFourZeroCoreNoncentralSocleUpgrade block P 16 10 := by
  intro hr hD hs hhead N hretained
  let bounds : DegreeFourZeroCoreNoncentralSocleBounds block P 10 :=
    degreeFourZeroCoreNoncentralSocleBounds_of_binary block P hMN hr hD
      (by omega) (by
        rw [hs]
        norm_num [degreeFourSocleSlots]) (by
          intro K _hK
          have hbinary :=
            degreeFourZeroCore_noncentralBinary_normalGen_le_schurSlots
              block P hTraceyPerm hr hD (Or.inr hs) K
          have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
          simpa only [DegreeFourBinarySocle, hp, hs,
            degreeFourZeroCoreSchurSlots] using hbinary)
  exact (degreeFourZeroCoreNoncentralSocleUpgrade_of_bounds
    (framePoints := 16) block P bounds) hr hD hs hhead N hretained

/-- Checked common bridge used by every literal eight-block frame row. -/
noncomputable def degreeFourZeroCoreEightNoncentralSocleBridge
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    DegreeFourZeroCoreFixedFrameNoncentralSocleBridge block P 8 5 :=
  degreeFourZeroCoreFixedFrameNoncentralSocleBridge_of_upgrade block P
    (degreeFourZeroCoreEightNoncentralSocleUpgrade
      block P hMN hTraceyPerm)

/-- Checked common bridge used by every literal sixteen-block frame row. -/
noncomputable def degreeFourZeroCoreSixteenNoncentralSocleBridge
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    DegreeFourZeroCoreFixedFrameNoncentralSocleBridge block P 16 10 :=
  degreeFourZeroCoreFixedFrameNoncentralSocleBridge_of_upgrade block P
    (degreeFourZeroCoreSixteenNoncentralSocleUpgrade
      block P hMN hTraceyPerm)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
