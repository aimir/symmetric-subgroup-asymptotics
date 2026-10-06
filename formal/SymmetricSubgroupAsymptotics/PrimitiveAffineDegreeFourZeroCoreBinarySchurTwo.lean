import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreBinarySchurThree
import SymmetricSubgroupAsymptotics.Non2SchurCyclicThreeOrbit
import SymmetricSubgroupAsymptotics.SylowPrimePowerTransitive
import SymmetricSubgroupAsymptotics.BinaryRestrictedInducedHead

/-!
# The exceptional two-dimensional binary Schur row

The nonfixed `(h,e)=(2,1)` row has quotient image `C3`.  Its pulled-back
kernel is transitive on eight or sixteen blocks.  A transitive binary
subgroup of that kernel is obtained from an actual Sylow subgroup.  Mackey
restriction of the literal induced two-space and the binary-grid theorem
then give head at most `3s/4`, hence `8 m_E <= 3s`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance degreeFourBinarySchurTwo_profilePrimeFact :
    Fact P.p.Prime := ⟨P.p_prime⟩

private noncomputable def degreeFourZeroCoreBinaryScalarCap (s : ℕ) : ℕ :=
  3 * s / 4

set_option maxHeartbeats 800000 in
/-- The scalar two-dimensional row obeys the sharp translation
multiplicity inequality on both surviving finite frames. -/
theorem degreeFourBinaryTranslation_schurTwo_le_blocks
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : Nat.card block.Points = 8 ∨ Nat.card block.Points = 16)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (S : Submodule
      (ZMod P.p)[
        DegreeFourRetainedQuotient N ⧸ DegreeFourBinarySocle block P N]
      (DegreeFourBinarySocleChart block P N).quotientRepresentation.ρ.asModule)
    [IsSimpleModule
      (ZMod P.p)[
        DegreeFourRetainedQuotient N ⧸ DegreeFourBinarySocle block P N] S]
    [FiniteDimensional
      (ZMod P.p)
      (DegreeFourBinaryTargetSection block P N).asSubmodule]
    (hnonfixed : ¬ representationSubmoduleFixed
      (DegreeFourBinarySocleChart block P N).quotientRepresentation.ρ S)
    (hS : Module.finrank
      (ZMod P.p) S = 2)
    (hSE : Module.finrank
      (Module.End
        (ZMod P.p)[
          DegreeFourRetainedQuotient N ⧸
          DegreeFourBinarySocle block P N]
        S) S = 1) :
    8 * schurSocleMultiplicity
        (k := ZMod P.p)
        (R := (ZMod P.p)[
          DegreeFourRetainedQuotient N ⧸
          DegreeFourBinarySocle block P N])
        (A := (DegreeFourBinaryTargetSection block P N).asSubmodule)
        (X := S) ≤ 3 * Nat.card block.Points := by
  let G := preE7NonPairAction w U
  let Q := DegreeFourRetainedQuotient N
  let A := DegreeFourBinarySocle block P N
  let C := DegreeFourBinarySocleChart block P N
  let sigma := C.quotientRepresentation.ρ
  let T := DegreeFourBinaryTargetSection block P N
  let phi := degreeFourBinarySocleTopMap block P N
  have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
  have hcard : Nat.card (ZMod P.p) = 2 := by
    rw [Nat.card_zmod, hp]
  letI : FiniteDimensional (ZMod P.p) C.quotientRepresentation := by
    simpa only [C, DegreeFourBinarySocleChart,
      selectedPrimeSoclePartElementaryChart] using C.finiteDimensional
  let K : Subgroup G := (schurSimpleActionKernel sigma S).comap phi
  have hphi : Function.Surjective phi :=
    (QuotientGroup.mk'_surjective A).comp
      (QuotientGroup.mk'_surjective N.1)
  let i : block.Points := block.base
  have hclasses : Nat.card
      (MulAction.orbitRel.Quotient K block.Points) = 1 := by
    simpa only [C, DegreeFourBinarySocleChart,
      selectedPrimeSoclePartElementaryChart] using
      (schurSimpleActionKernel_comap_orbit_classes_eq_one_of_card_eight_or_sixteen_generic
        hcard i sigma S phi hphi hnonfixed hS hSE hs)
  letI : MulAction.IsPretransitive K block.Points :=
    isPretransitive_of_orbitQuotient_card_eq_one hclasses
  obtain ⟨P₂, hP₂, hP₂K, hP₂trans⟩ :=
    exists_transitive_binarySubgroup_of_card_eight_or_sixteen K hs
  letI : MulAction.IsPretransitive P₂ block.Points := hP₂trans
  have hH0 : (initialState hTraceyPerm block).topPointStabilizer i =
      MulAction.stabilizer (preE7NonPairAction w U) i := by
    apply Subgroup.ext
    intro g
    rfl
  have hpre : MulAction.IsPretransitive P₂
      ((initialState hTraceyPerm block).A ⧸
        (initialState hTraceyPerm block).topPointStabilizer i) := by
    change MulAction.IsPretransitive P₂
      ((preE7NonPairAction w U) ⧸
        (initialState hTraceyPerm block).topPointStabilizer i)
    exact hH0.symm ▸
      stabilizerCosets_isPretransitive_of_isPretransitive P₂ i
  let localRep := degreeFourZeroCoreLocalRepresentation block P hTraceyPerm i
  have hlocalDim : Module.finrank
      (ZMod (localTranslationChart block P).p)
      (localTranslationChart block P).V = 2 := by
    change (chart block P).d = 2
    exact (degreeFour_translationDimension block P hr).2
  have hindex :
      ((initialState hTraceyPerm block).topPointStabilizer i).index =
        Nat.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using
      (initialState hTraceyPerm block).topPointStabilizer_index i
  have hdegree :
      ((initialState hTraceyPerm block).topPointStabilizer i).index = 8 ∨
      ((initialState hTraceyPerm block).topPointStabilizer i).index = 16 :=
    hs.imp (hindex.trans ·) (hindex.trans ·)
  let Vambient :=
    PermutationalWreathProduct.Compression.ElementarySubmodule
      (p := (localTranslationChart block P).p)
      (initialState hTraceyPerm block).rho (localMap block P)
      (localTranslationChart block P).equiv.symm
  letI : FiniteDimensional (ZMod P.p) Vambient := by
    change FiniteDimensional (ZMod (localTranslationChart block P).p)
      Vambient
    exact FiniteDimensional.of_injective
      (Submodule.subtype Vambient) Vambient.subtype_injective
  let ambient := degreeFourZeroCoreAmbientRepresentation
    block P hTraceyPerm
  let induced := degreeFourZeroCoreInducedRepresentation
    block P hTraceyPerm i
  let f₀ := degreeFourZeroCoreInducedIntertwiner
    block P hTraceyPerm i
  let fP₂ := representationRestrictionHom ambient induced P₂.subtype f₀
  have hfP₂ : Function.Injective fP₂ := by
    simpa only [fP₂, f₀, representationRestrictionHom] using
      (degreeFourZeroCoreInducedIntertwiner_injective
        block P hTraceyPerm i)
  have hinduced : UniformSubrepresentationHeadBound
      (induced.comp P₂.subtype)
      (degreeFourZeroCoreBinaryScalarCap (Nat.card block.Points)) := by
    intro M
    have hfour :=
      inducedTwoSpace_binaryTransitiveRestriction_four_mul_characterHead_le_three_mul_index_explicit
      (H := (initialState hTraceyPerm block).topPointStabilizer i)
        (P := P₂) (hP := hP₂) (rho := localRep)
        (hdim := hlocalDim) (hpre := hpre)
        (hdegree := hdegree) (M := M)
    rw [(representationCharacterHeadEquiv M.toRepresentation).finrank_eq]
      at hfour
    rcases hs with hs | hs <;>
      simp only [degreeFourZeroCoreBinaryScalarCap, hs] <;> omega
  have hP₂ambient : UniformSubrepresentationHeadBound
      (ambient.comp P₂.subtype)
      (degreeFourZeroCoreBinaryScalarCap (Nat.card block.Points)) :=
    uniformSubrepresentationHeadBound_of_injective
      (ambient.comp P₂.subtype)
      (induced.comp P₂.subtype)
      fP₂ hfP₂ _ hinduced
  let inclusion : P₂ →* K := {
    toFun := fun g ↦ ⟨g.1, hP₂K g.2⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl }
  have hambient : UniformSubrepresentationHeadBound
      (ambient.comp K.subtype)
      (degreeFourZeroCoreBinaryScalarCap (Nat.card block.Points)) := by
    intro M
    let MP₂ : Subrepresentation
        (ambient.comp P₂.subtype) := {
      toSubmodule := M.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        exact M.apply_mem_toSubmodule (inclusion g) hv }
    have hrestrict :=
      (representationRestrictionHom M.toRepresentation
        (Representation.trivial
          (ZMod (localTranslationChart block P).p) K
          (ZMod (localTranslationChart block P).p)) inclusion).finrank_le_finrank_of_injective
        (representationRestrictionHom_injective _ _ _)
    have hrestrict' : Module.finrank
        (ZMod (localTranslationChart block P).p)
        (M.toRepresentation.IntertwiningMap
          (Representation.trivial
            (ZMod (localTranslationChart block P).p) K
            (ZMod (localTranslationChart block P).p))) ≤
        Module.finrank (ZMod (localTranslationChart block P).p)
          (MP₂.toRepresentation.IntertwiningMap
            (Representation.trivial
              (ZMod (localTranslationChart block P).p) P₂
              (ZMod (localTranslationChart block P).p))) := by
      simpa only [MP₂, inclusion, MonoidHom.coe_comp,
        Function.comp_apply] using hrestrict
    exact hrestrict'.trans (hP₂ambient MP₂)
  let M0 := DegreeFourBinarySourceSection block P N
  let M : Subrepresentation ambient :=
    ActualWreathAffineCapacity.subrepresentationComp
      (QuotientGroup.mk' (E block P))
      (elementaryChart block P).quotientRepresentation.ρ M0
  let theta := T.toRepresentation
  let q : M.toRepresentation.IntertwiningMap (theta.comp phi) := by
    simpa only [M, M0, theta, T, ambient,
      degreeFourZeroCoreAmbientRepresentation, initialState,
      localTranslationChart, elementaryChart,
      ActualWreathAffineCapacity.ambientRepresentation,
      ActualWreathAffineCapacity.E,
      PermutationalWreathProduct.Compression.kernelElementaryChart,
      DegreeFourBinarySourceSectionInflated] using
        (degreeFourBinaryTranslationSectionIntertwiner block P N)
  have hqsurj : Function.Surjective q := by
    simpa only [q, M, M0, theta, T, ambient,
      degreeFourZeroCoreAmbientRepresentation, initialState,
      localTranslationChart, elementaryChart,
      ActualWreathAffineCapacity.ambientRepresentation,
      ActualWreathAffineCapacity.E,
      PermutationalWreathProduct.Compression.kernelElementaryChart,
      DegreeFourBinarySourceSectionInflated] using
        (degreeFourBinaryTranslationSectionLinearMap_surjective block P N)
  have hrow := schurTargetIsotypic_finrank_le_of_kernel_section_head
    (k := ZMod P.p) sigma S theta phi K rfl ambient M q hqsurj
      (degreeFourZeroCoreBinaryScalarCap (Nat.card block.Points)) hambient
  rw [hS] at hrow
  let eT : T.asSubmodule ≃ₗ[(ZMod P.p)[Q ⧸ A]]
      T.toRepresentation.asModule := by
    simpa only using
      (submoduleRepresentationModuleEquiv sigma T.asSubmodule)
  letI : FiniteDimensional (ZMod P.p) S :=
    FiniteDimensional.of_injective
      (S.subtype.restrictScalars (ZMod P.p)) S.subtype_injective
  have hm := schurSocleMultiplicity_eq_of_target_linearEquiv
    (k := ZMod P.p) (R := (ZMod P.p)[Q ⧸ A]) (X := S) eT.symm
  rw [hm] at hrow
  rcases hs with hs | hs <;>
    simp only [theta, T, C, Q, A, DegreeFourBinarySocleChart,
      selectedPrimeSoclePartElementaryChart,
      degreeFourZeroCoreBinaryScalarCap, hs]
      at hrow ⊢ <;> omega

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
