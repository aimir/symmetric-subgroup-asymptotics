import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreBinaryNoFixed
import SymmetricSubgroupAsymptotics.SchurKernelTargetSectionHead
import SymmetricSubgroupAsymptotics.Non2SchurCyclicSevenOrbit
import SymmetricSubgroupAsymptotics.TransitiveInducedDerangementHead
import SymmetricSubgroupAsymptotics.InducedTernaryHead
import SymmetricSubgroupAsymptotics.SchurMultiplicityTargetEquiv
import SymmetricSubgroupAsymptotics.OrbitQuotientOneTransitive
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentTransfer
import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationLayerSource

/-!
# The exceptional three-dimensional binary Schur row

The scalar `(h,e)=(3,1)` row has quotient image `C7`.  At eight or sixteen
blocks its pulled-back row kernel is transitive.  The actual correlated
translation module embeds in the induced local two-space, so the literal
translation section has head at most the number of blocks.  The target
section theorem turns this into `3 m_E <= s`.
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

local instance degreeFourBinarySchurThree_profilePrimeFact :
    Fact P.p.Prime := ⟨P.p_prime⟩

noncomputable def degreeFourZeroCoreLocalRepresentation
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (i : block.Points) :
    Representation (ZMod (localTranslationChart block P).p)
      ((initialState hTraceyPerm block).topPointStabilizer i)
      (localTranslationChart block P).V :=
  ActualWreathAffineCapacity.localRepresentation
    (initialState hTraceyPerm block) (localMap block P)
    (localTranslationChart block P) i

noncomputable def degreeFourZeroCoreAmbientRepresentation
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    Representation (ZMod (localTranslationChart block P).p)
      (preE7NonPairAction w U)
      (PermutationalWreathProduct.Compression.ElementarySubmodule
        (p := (localTranslationChart block P).p)
        (initialState hTraceyPerm block).rho (localMap block P)
        (localTranslationChart block P).equiv.symm) :=
  ActualWreathAffineCapacity.ambientRepresentation
    (initialState hTraceyPerm block) (localMap block P)
    (localTranslationChart block P)

noncomputable def degreeFourZeroCoreInducedRepresentation
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (i : block.Points) :
    Representation (ZMod (localTranslationChart block P).p)
      (preE7NonPairAction w U)
      (Representation.IndV
        ((initialState hTraceyPerm block).topPointStabilizer i).subtype
        (degreeFourZeroCoreLocalRepresentation block P hTraceyPerm i)) :=
  ActualWreathAffineCapacity.inducedRepresentation
    (initialState hTraceyPerm block) (localMap block P)
    (localTranslationChart block P) i

noncomputable def degreeFourZeroCoreInducedIntertwiner
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (i : block.Points) :
    (degreeFourZeroCoreAmbientRepresentation block P hTraceyPerm).IntertwiningMap
      (degreeFourZeroCoreInducedRepresentation block P hTraceyPerm i) :=
  ActualWreathAffineCapacity.inducedIntertwiner
    (initialState hTraceyPerm block) (localMap block P)
    (localTranslationChart block P) i

theorem degreeFourZeroCoreInducedIntertwiner_injective
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (i : block.Points) :
    Function.Injective
      (degreeFourZeroCoreInducedIntertwiner block P hTraceyPerm i) :=
  ActualWreathAffineCapacity.inducedIntertwiner_injective
    (initialState hTraceyPerm block) (localMap block P)
    (localTranslationChart block P) i

/-- Explicit-instance form of the transitive restricted induced-head row.
Passing the coset transitivity proof as data prevents large affine aliases
from obscuring the corresponding typeclass during downstream elaboration. -/
theorem inducedTwoSpace_restricted_subrepresentationHead_le_index_explicit
    {p : ℕ} [Fact p.Prime]
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (H P₀ : Subgroup G) (rho : Representation (ZMod p) H V)
    (hdim : Module.finrank (ZMod p) V = 2)
    (hpre : MulAction.IsPretransitive P₀ (G ⧸ H))
    (hindex : 2 ≤ H.index)
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp P₀.subtype)) :
    Module.finrank (ZMod p)
        (M.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod p) P₀ (ZMod p))) ≤ H.index := by
  letI : MulAction.IsPretransitive P₀ (G ⧸ H) := hpre
  exact inducedTwoSpace_restricted_subrepresentationHead_le_index
    H P₀ rho hdim hindex M

set_option maxHeartbeats 800000 in
/-- The scalar three-dimensional row obeys the sharp translation
multiplicity inequality on both surviving finite frames. -/
theorem degreeFourBinaryTranslation_schurThree_le_blocks
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : Nat.card block.Points = 8 ∨ Nat.card block.Points = 16)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (S : Submodule
      (ZMod P.p)[DegreeFourRetainedQuotient N ⧸
        DegreeFourBinarySocle block P N]
      (DegreeFourBinarySocleChart block P N).quotientRepresentation.ρ.asModule)
    [IsSimpleModule
      (ZMod P.p)[DegreeFourRetainedQuotient N ⧸
        DegreeFourBinarySocle block P N] S]
    [FiniteDimensional
      (ZMod P.p)
      (DegreeFourBinaryTargetSection block P N).asSubmodule]
    (hnonfixed : ¬ representationSubmoduleFixed
      (DegreeFourBinarySocleChart block P N).quotientRepresentation.ρ S)
    (hS : Module.finrank (ZMod P.p) S = 3)
    (hSE : Module.finrank
      (Module.End
        (ZMod P.p)[DegreeFourRetainedQuotient N ⧸
          DegreeFourBinarySocle block P N]
        S) S = 1) :
    3 * schurSocleMultiplicity
        (k := ZMod P.p)
        (R := (ZMod P.p)[DegreeFourRetainedQuotient N ⧸
          DegreeFourBinarySocle block P N])
        (A := (DegreeFourBinaryTargetSection block P N).asSubmodule)
        (X := S) ≤ Nat.card block.Points := by
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
      (schurSimpleActionKernel_comap_orbit_classes_eq_one_of_card_eight_or_sixteen
        hcard i sigma S phi hphi hnonfixed hS hSE hs)
  letI : MulAction.IsPretransitive K block.Points :=
    isPretransitive_of_orbitQuotient_card_eq_one hclasses
  have hH0 : (initialState hTraceyPerm block).topPointStabilizer i =
      MulAction.stabilizer (preE7NonPairAction w U) i := by
    apply Subgroup.ext
    intro g
    rfl
  have hpre : MulAction.IsPretransitive K
      ((initialState hTraceyPerm block).A ⧸
        (initialState hTraceyPerm block).topPointStabilizer i) := by
    change MulAction.IsPretransitive K
      ((preE7NonPairAction w U) ⧸
        (initialState hTraceyPerm block).topPointStabilizer i)
    exact hH0.symm ▸
      stabilizerCosets_isPretransitive_of_isPretransitive K i
  let localRep := degreeFourZeroCoreLocalRepresentation block P hTraceyPerm i
  have hlocalDim : Module.finrank
      (ZMod (localTranslationChart block P).p)
      (localTranslationChart block P).V = 2 := by
    change (chart block P).d = 2
    exact (degreeFour_translationDimension block P hr).2
  have hindex : 2 ≤
      ((initialState hTraceyPerm block).topPointStabilizer i).index := by
    rw [show ((initialState hTraceyPerm block).topPointStabilizer i).index =
        Nat.card block.Points by
      simpa only [Fintype.card_eq_nat_card] using
        (initialState hTraceyPerm block).topPointStabilizer_index i]
    rcases hs with hs | hs <;> omega
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
  let fK := representationRestrictionHom ambient induced K.subtype f₀
  have hfK : Function.Injective fK := by
    simpa only [fK, f₀, representationRestrictionHom] using
      (degreeFourZeroCoreInducedIntertwiner_injective
        block P hTraceyPerm i)
  have hinduced : UniformSubrepresentationHeadBound
      (induced.comp K.subtype)
      (Nat.card block.Points) := by
    intro M
    have hM := inducedTwoSpace_restricted_subrepresentationHead_le_index_explicit
      (H := (initialState hTraceyPerm block).topPointStabilizer i)
      (P₀ := K) (rho := localRep) (hdim := hlocalDim)
      (hpre := hpre) (hindex := hindex) (M := M)
    simpa only [ActualWreathCompressionState.topPointStabilizer_index,
      Fintype.card_eq_nat_card, induced,
      degreeFourZeroCoreInducedRepresentation,
      degreeFourZeroCoreLocalRepresentation, localRep] using hM
  have hambient : UniformSubrepresentationHeadBound
      (ambient.comp K.subtype)
      (Nat.card block.Points) :=
    uniformSubrepresentationHeadBound_of_injective
      (ambient.comp K.subtype)
      (induced.comp K.subtype)
      fK hfK (Nat.card block.Points) hinduced
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
  have hq : Function.Surjective q := by
    simpa only [q, M, M0, theta, T, ambient,
      degreeFourZeroCoreAmbientRepresentation, initialState,
      localTranslationChart, elementaryChart,
      ActualWreathAffineCapacity.ambientRepresentation,
      ActualWreathAffineCapacity.E,
      PermutationalWreathProduct.Compression.kernelElementaryChart,
      DegreeFourBinarySourceSectionInflated] using
        (degreeFourBinaryTranslationSectionLinearMap_surjective block P N)
  have hrow := schurTargetIsotypic_finrank_le_of_kernel_section_head
    (k := ZMod P.p) sigma S theta phi K rfl ambient M q hq
      (Nat.card block.Points) hambient
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
  simpa only [theta, T, C, Q, A, DegreeFourBinarySocleChart,
    selectedPrimeSoclePartElementaryChart] using hrow

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
