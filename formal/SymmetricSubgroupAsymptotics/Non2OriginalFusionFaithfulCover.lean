import SymmetricSubgroupAsymptotics.BinaryPairResidualTop
import SymmetricSubgroupAsymptotics.Non2OriginalFusionPayloadSelection

/-!
# Nonbinary fusion certificates through a faithful cover

The acting quotient of an arbitrary pair section is `B = U / (K ⊔ N)`.
It need not act faithfully on the original pair labels.  The literal pair
top `T` does act faithfully and maps onto `B`.  This file proves that the
complete nonbinary certificate constructed on the pulled-back `T`-module
descends to the original `B`-module, then builds the full original-extension
payload for every literal normal `N`, without assuming `N ≤ K`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

section Displacement

variable {k D B A : Type} [Field k] [Group D] [Group B]
variable [AddCommGroup A] [Module k A]

/-- Vanishing of a displacement slice descends along a surjective acting
group map.  Surjectivity is used pointwise, so no finite-group hypothesis is
needed. -/
theorem displacementSlice_eq_bot_of_comp_onto_eq_bot
    (ρ : Representation k B A) (σ : D →* B)
    (hσ : Function.Surjective σ) (C : Submodule k A)
    (hzero : displacementSlice (ρ.comp σ) C = ⊥) :
    displacementSlice ρ C = ⊥ := by
  apply le_bot_iff.mp
  intro f hf
  obtain ⟨a, rfl⟩ := hf.1
  have hmem : representationDisplacement (ρ.comp σ) a ∈
      displacementSlice (ρ.comp σ) C := by
    refine ⟨⟨a, rfl⟩, ?_⟩
    intro d
    exact hf.2 (σ d)
  rw [hzero] at hmem
  funext b
  obtain ⟨d, rfl⟩ := hσ b
  exact congrFun hmem d

/-- The full invariant displacement rank is unchanged after pullback along
a surjective acting-group map. -/
theorem displacementSlice_invariants_finrank_comp_onto
    [Finite D] [Finite B] [FiniteDimensional k A]
    (ρ : Representation k B A) (σ : D →* B)
    (hσ : Function.Surjective σ) :
    Module.finrank k
        (displacementSlice (ρ.comp σ)
          (Representation.invariants (ρ.comp σ))) =
      Module.finrank k (displacementSlice ρ ρ.invariants) := by
  rw [displacementSlice_invariants_finrank,
    displacementSlice_invariants_finrank]
  exact fullFixedQuotient_finrank_comp_onto ρ σ hσ

end Displacement

namespace Non2OriginalFusionCertificate

variable {D B : Type} [Group D] [Group B] [Finite D] [Finite B]

/-- A certificate proved on a faithful cover descends to the original
quotient module.  Fixed spaces, the retained annihilator, the quotient fixed
space and Schur capacity are all invariant under a surjective action map. -/
def of_surjective_cover
    (σ : D →* B) (hσ : Function.Surjective σ)
    (M : Rep (ZMod 2) B) [FiniteDimensional (ZMod 2) M]
    {s : ℕ}
    (C : Non2OriginalFusionCertificate
      (Rep.of (M.ρ.comp σ)) s) :
    Non2OriginalFusionCertificate M s := by
  have hInv : Representation.invariants (M.ρ.comp σ) = M.ρ.invariants :=
    representation_invariants_comp_onto M.ρ σ hσ
  have hInvRank :
      Module.finrank (ZMod 2)
          (Representation.invariants (M.ρ.comp σ)) =
        Module.finrank (ZMod 2) M.ρ.invariants :=
    congrArg
      (fun S : Submodule (ZMod 2) M => Module.finrank (ZMod 2) S)
      hInv
  let cut : {S : Submodule (ZMod 2) M // S ≤ M.ρ.invariants} :=
    ⟨C.cut.1, by
      intro a ha
      rw [← hInv]
      exact C.cut.2 ha⟩
  have hDisp :
      Module.finrank (ZMod 2)
          (displacementSlice (M.ρ.comp σ)
            (Representation.invariants (M.ρ.comp σ))) =
        Module.finrank (ZMod 2)
          (displacementSlice M.ρ M.ρ.invariants) :=
    displacementSlice_invariants_finrank_comp_onto M.ρ σ hσ
  have hCutRank :
      Module.finrank (ZMod 2) cut.1 =
        non2CentralCutDimension
          (Module.finrank (ZMod 2) M.ρ.invariants)
          (Module.finrank (ZMod 2)
            (displacementSlice M.ρ M.ρ.invariants)) := by
    dsimp only [cut]
    calc
      Module.finrank (ZMod 2) C.cut.1 =
          non2CentralCutDimension
            (Module.finrank (ZMod 2)
              (Representation.invariants (M.ρ.comp σ)))
            (Module.finrank (ZMod 2)
              (displacementSlice (M.ρ.comp σ)
                (Representation.invariants (M.ρ.comp σ)))) := C.cut_finrank
      _ = non2CentralCutDimension
            (Module.finrank (ZMod 2) M.ρ.invariants)
            (Module.finrank (ZMod 2)
              (displacementSlice M.ρ M.ρ.invariants)) := by
        rw [hInvRank, hDisp]
  have hZero : displacementSlice M.ρ cut.1 = ⊥ :=
    displacementSlice_eq_bot_of_comp_onto_eq_bot
      M.ρ σ hσ C.cut.1 C.displacement_zero
  have hQuotient :
      Module.finrank (ZMod 2)
          (OriginalCentralCutExtension.quotientModule M cut).ρ.invariants =
        Module.finrank (ZMod 2) M.ρ.invariants -
          non2CentralCutDimension
            (Module.finrank (ZMod 2) M.ρ.invariants)
            (Module.finrank (ZMod 2)
              (displacementSlice M.ρ M.ρ.invariants)) := by
    calc
      Module.finrank (ZMod 2)
          (OriginalCentralCutExtension.quotientModule M cut).ρ.invariants =
          Module.finrank (ZMod 2) M.ρ.invariants -
            Module.finrank (ZMod 2) cut.1 := by
        change Module.finrank (ZMod 2)
          (centralQuotientRepresentation M.ρ cut.1 cut.2).invariants = _
        exact centralQuotient_invariants_finrank_of_slice_eq_bot
          M.ρ cut.1 cut.2 hZero
      _ = Module.finrank (ZMod 2) M.ρ.invariants -
          non2CentralCutDimension
            (Module.finrank (ZMod 2) M.ρ.invariants)
            (Module.finrank (ZMod 2)
              (displacementSlice M.ρ M.ρ.invariants)) := by rw [hCutRank]
  have hCap :
      OriginalCentralCutFusion.capacity
          (Rep.of (M.ρ.comp σ)) C.cut =
        OriginalCentralCutFusion.capacity M cut := by
    unfold OriginalCentralCutFusion.capacity
      OriginalCentralCutExtension.quotientModule
    simpa only [cut] using
      (representationSchurCapacity_comp σ hσ
        (centralQuotientRepresentation M.ρ cut.1 cut.2))
  refine {
    fixed_budget := ?_
    cut := cut
    cut_finrank := ?_
    displacement_zero := ?_
    quotient_invariants := ?_
    cost_le := ?_
    gap_ge := ?_ }
  · rw [← hInv]
    exact C.fixed_budget
  · exact hCutRank
  · exact hZero
  · exact hQuotient
  · dsimp only [cut]
    rw [← hCap]
    exact C.cost_le
  · unfold OriginalCentralCutFusion.gapParameter
      OriginalCentralCutFusion.prefixDegree
    dsimp only [cut] at hCap ⊢
    rw [← hCap]
    exact C.gap_ge

end Non2OriginalFusionCertificate

section FaithfulCover

variable {T B X : Type} [Group T] [Group B] [Finite T] [Finite B]
variable [Finite X] [MulAction T X] [FaithfulSMul T X]
variable [MulAction.IsPretransitive T X]

/-- Construct the reusable certificate on a faithful transitive cover and
descend it to the original quotient module. -/
theorem exists_non2OriginalFusionCertificate_of_faithfulCover
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (topBase : T →* B) (topBase_surjective : Function.Surjective topBase)
    (hT : ¬ IsPGroup 2 T) (x : X)
    (M : Rep (ZMod 2) B) [FiniteDimensional (ZMod 2) M]
    (P : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) T X))
    (qmap : P.toRepresentation.IntertwiningMap (M.ρ.comp topBase))
    (qmap_surjective : Function.Surjective qmap)
    (hs : 24 ≤ Nat.card X) (heven : Even (Nat.card X)) :
    Nonempty (Non2OriginalFusionCertificate M (Nat.card X)) := by
  have hcover : Nonempty (Non2OriginalFusionCertificate
      (Rep.of (M.ρ.comp topBase)) (Nat.card X)) := by
    simpa using
      (exists_non2OriginalFusionCertificate
        hTracey hExceptional hT x (Rep.of (M.ρ.comp topBase))
          P qmap qmap_surjective hs heven)
  exact hcover.map
    (Non2OriginalFusionCertificate.of_surjective_cover
      topBase topBase_surjective M)

end FaithfulCover

end SymmetricSubgroupAsymptotics

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

section Payload

variable {s : ℕ} {U : Subgroup (Equiv.Perm (Fin (2 * s)))}
variable (F : BinaryPairFrame U (Fin s))
variable (N : {N : Subgroup U // N.Normal})
variable [MulAction.IsPretransitive F.top.range (Fin s)]

/-- Complete original-weight payload for every literal normal axis of a
nonbinary pair action.  The section is `K/(K ∩ N)` and the acting quotient is
`U/(K ⊔ N)`; no containment of `N` in the pair kernel is assumed. -/
theorem exists_non2OriginalFusionAxisPayload_of_arbitraryPairAxis
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hTop : ¬ IsPGroup 2 F.top.range)
    (i : Fin s) (hs : 24 ≤ s) (heven : Even s) :
    Nonempty (Non2OriginalFusionAxisPayload s U N) := by
  letI : N.1.Normal := N.2
  have hcertificate : Nonempty
      (Non2OriginalFusionCertificate
        (Rep.of (F.sectionRepresentation N.1)) s) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      (exists_non2OriginalFusionCertificate_of_faithfulCover
        hTracey hExceptional
        (F.sectionTopQuotient N.1) (F.sectionTopQuotient_surjective N.1)
        hTop i (Rep.of (F.sectionRepresentation N.1))
        F.kernelTopPermutationSubrepresentation
        (F.sectionTopIntertwiner N.1)
        (F.normalSpace N.1).mkQ_surjective
        (by simpa using hs) (by simpa using heven))
  obtain ⟨C⟩ := hcertificate
  exact ⟨{
    B := U ⧸ (F.top.ker ⊔ N.1)
    M := Rep.of (F.sectionRepresentation N.1)
    certificate := C
    base := F.zeroCutBase N.1
    base_surjective := F.zeroCutBase_surjective N.1
    moduleChart := F.sectionModuleChart N.1
    T := F.top.range
    topAction := F.top.range.subtype
    topAction_injective := Subtype.val_injective
    topBase := F.sectionTopQuotient N.1
    topBase_surjective := F.sectionTopQuotient_surjective N.1 }⟩

end Payload

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
