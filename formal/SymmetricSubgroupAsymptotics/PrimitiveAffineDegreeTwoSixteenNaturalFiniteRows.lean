import SymmetricSubgroupAsymptotics.BinaryPairLiteralTopQuotient
import SymmetricSubgroupAsymptotics.FiniteThreeNormalChainSocleGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopConcreteBranches
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopStructuralAnchor
import SymmetricSubgroupAsymptotics.SimpleChiefFamilies
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber
import Mathlib.GroupTheory.Perm.Fin

/-!
# Finite packages for the natural count-sixteen tops

The natural `A_16` and `S_16` cases do not need data indexed by the
original pair action or by its realizations.  For each of the two literal
tops it is enough to retain:

* a uniformly padded two-generator socle certificate for every quotient of
  that literal top; and
* a four-generator theorem for every invariant submodule of its natural
  binary permutation module.

The generic converter below transports these two literal-top facts through
an arbitrary natural-top realization and applies the same Schur extension
theorem as the finite one-frame catalogue.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoSixteenNaturalFiniteRows

/-- The literal permutation group attached to one natural-top kind. -/
def naturalTopSubgroup (kind : DegreeTwoSixteenNaturalTop) :
    Subgroup (Equiv.Perm (Fin 16)) :=
  match kind with
  | .alternating => alternatingGroup (Fin 16)
  | .symmetric => ⊤

/-! ## Structural quotient-socle certificates -/

/-- Every quotient of the natural alternating top has a padded two-place
socle generator.  The only two normal states are handled symbolically; no
enumeration of `A_16` is involved. -/
noncomputable def alternatingTopSocle :
    ∀ N : {N : Subgroup (alternatingGroup (Fin 16)) // N.Normal},
      SocleNormalGeneratorBound
        (alternatingGroup (Fin 16) ⧸ N.1) 2 := by
  letI : IsSimpleGroup (alternatingGroup (Fin 16)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  intro N
  rcases N.2.eq_bot_or_eq_top with hbot | htop
  · let e : alternatingGroup (Fin 16) ⧸ N.1 ≃*
        alternatingGroup (Fin 16) :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans
        QuotientGroup.quotientBot
    letI : IsSimpleGroup (alternatingGroup (Fin 16) ⧸ N.1) :=
      e.isSimpleGroup
    exact (socleNormalGeneratorBound_one_of_isSimpleGroup _).mono
      (by norm_num)
  · letI : Subsingleton
        (alternatingGroup (Fin 16) ⧸ (⊤ :
          Subgroup (alternatingGroup (Fin 16)))) :=
      QuotientGroup.subsingleton_quotient_top
    letI : Subsingleton (alternatingGroup (Fin 16) ⧸ N.1) :=
      (QuotientGroup.quotientMulEquivOfEq htop).toEquiv.subsingleton
    exact (socleNormalGeneratorBound_one_of_subsingleton _).mono
      (by norm_num)

/-- The literal normal chain `1 < A_16 < S_16`, with a three-cycle as its
distinguished normal generator.  Simplicity of `A_16` and its index two in
`S_16` give the complete normal-lattice statement. -/
noncomputable def symmetricNormalChain :
    FiniteThreeNormalChainData (Equiv.Perm (Fin 16)) := by
  letI : IsSimpleGroup (alternatingGroup (Fin 16)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  let cycle : Equiv.Perm (Fin 16) := Fin.cycleRange 2
  have hcycle : Equiv.Perm.IsThreeCycle cycle :=
    Fin.isThreeCycle_cycleRange_two
  refine
    { middle := alternatingGroup (Fin 16)
      middle_normal := inferInstance
      middle_ne_bot :=
        (Subgroup.isSimpleGroup_iff.mp
          (show IsSimpleGroup (alternatingGroup (Fin 16)) from
            inferInstance)).1
      middle_ne_top := ?_
      normal_eq_bot_or_middle_or_top := ?_
      generator := cycle
      generator_mem := hcycle.mem_alternatingGroup
      generator_ne_one := hcycle.ne_one }
  · intro htop
    have hindex := alternatingGroup.index_eq_two (α := Fin 16)
    rw [htop, Subgroup.index_top] at hindex
    omega
  · intro N hN
    by_cases hbot : N = ⊥
    · exact Or.inl hbot
    · right
      letI : N.Normal := hN
      haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hbot
      exact indexTwo_maximal (alternatingGroup (Fin 16))
        alternatingGroup.index_eq_two N
        (Equiv.Perm.alternatingGroup_le_of_normal
          (by norm_num) inferInstance)

/-- Every quotient of the natural symmetric top has a padded two-place
socle generator.  The bottom, alternating, and top normal states are
dispatched through the structural three-state chain. -/
noncomputable def symmetricTopSocle :
    ∀ N : {N : Subgroup (naturalTopSubgroup .symmetric) // N.Normal},
      SocleNormalGeneratorBound
        (naturalTopSubgroup .symmetric ⧸ N.1) 2 :=
  (symmetricNormalChain.mapEquiv
    (Subgroup.topEquiv :
      (⊤ : Subgroup (Equiv.Perm (Fin 16))) ≃* Equiv.Perm (Fin 16)).symm).quotientSocleGeneratorBound_two

/-- The two finite theorem families needed for one natural top.  Both
fields are independent of the original pair action and of a chosen
realization. -/
structure DegreeTwoSixteenNaturalFiniteRowData
    (kind : DegreeTwoSixteenNaturalTop) : Type 1 where
  topSocle : ∀ N :
      {N : Subgroup (naturalTopSubgroup kind) // N.Normal},
    SocleNormalGeneratorBound
      (naturalTopSubgroup kind ⧸ N.1) 2
  natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation
      (ZMod 2) (naturalTopSubgroup kind) (Fin 16)) 4

namespace DegreeTwoSixteenNaturalTopRealization

variable {kind : DegreeTwoSixteenNaturalTop}
  {p : PreE7PairActionClass 16}
  (R : DegreeTwoSixteenNaturalTopRealization kind p)

/-- The equality in a natural-top realization gives the literal-to-actual
top equivalence without any generated catalogue interface. -/
noncomputable def topEquiv :
    naturalTopSubgroup kind ≃* R.frame.top.range :=
  MulEquiv.subgroupCongr (by
    simpa only [naturalTopSubgroup] using R.top_eq.symm)

/-- The natural permutation action is the coordinate action of the actual
pair frame after transport along `topEquiv`. -/
theorem module_action_eq (g : naturalTopSubgroup kind)
    (v : Fin 16 → ZMod 2) :
    permutationFunctionRepresentation
        (ZMod 2) (naturalTopSubgroup kind) (Fin 16) g v =
      R.frame.coordinateTopAction (DegreeTwoSixteenNaturalTopRealization.topEquiv R g) v := by
  funext i
  rfl

end DegreeTwoSixteenNaturalTopRealization

namespace DegreeTwoSixteenNaturalFiniteRowData

/-- The common natural-top profile, padded to the same `(2,4)` row used by
all literal one-frame count-sixteen tops. -/
def naturalProfile : DegreeTwoPairRelativeProfile :=
  degreeTwoPairOrdinaryRelativeProfile 2 4

variable {kind : DegreeTwoSixteenNaturalTop}
  {p : PreE7PairActionClass 16}
  (D : DegreeTwoSixteenNaturalFiniteRowData kind)
  (R : DegreeTwoSixteenNaturalTopRealization kind p)

/-- Named assembly boundary for one independently emitted natural-top
package. -/
noncomputable def ofCertificates
    (topSocle : ∀ N :
      {N : Subgroup (naturalTopSubgroup kind) // N.Normal},
      SocleNormalGeneratorBound
        (naturalTopSubgroup kind ⧸ N.1) 2)
    (natural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation
        (ZMod 2) (naturalTopSubgroup kind) (Fin 16)) 4) :
    DegreeTwoSixteenNaturalFiniteRowData kind where
  topSocle := topSocle
  natural := natural

/-- The natural alternating package needs only its finite module
certificate; the quotient-socle field is supplied by the structural
two-normal-state theorem above. -/
noncomputable def alternatingOfNaturalModule
    (natural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation
        (ZMod 2) (naturalTopSubgroup .alternating) (Fin 16)) 4) :
    DegreeTwoSixteenNaturalFiniteRowData .alternating :=
  ofCertificates alternatingTopSocle natural

/-- The natural symmetric package needs only its finite module certificate;
the quotient-socle field comes from `1 < A_16 < S_16`. -/
noncomputable def symmetricOfNaturalModule
    (natural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation
        (ZMod 2) (naturalTopSubgroup .symmetric) (Fin 16)) 4) :
    DegreeTwoSixteenNaturalFiniteRowData .symmetric :=
  ofCertificates symmetricTopSocle natural

/-- Transport the literal-top socle and module certificates through one
actual original-normal quotient. -/
noncomputable def envelope
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (N : {N : Subgroup (preE7PairAction 16 p) // N.Normal}) :
    DegreeTwoPairRelativeQuotientEnvelope
      (preE7PairAction 16 p ⧸ N.1) naturalProfile := by
  letI : N.1.Normal := N.2
  let e := DegreeTwoSixteenNaturalTopRealization.topEquiv R
  let topNormal :
      {M : Subgroup (naturalTopSubgroup kind) // M.Normal} :=
    ⟨R.frame.literalTopNormal e N.1,
      R.frame.literalTopNormal_normal e N.1⟩
  let top :=
    (DegreeTwoPairBinaryKernelAnchor.ofSocleGeneratorBound hZmud
      (D.topSocle topNormal)).toQuotientEnvelope lit
  let transported := top.ofTargetEquiv
    (R.frame.zeroCutBaseEquivLiteralTop e N.1)
  exact degreeTwoPairSchurLiftEnvelope
    (R.frame.zeroCutBase N.1) (R.frame.zeroCutBase_surjective N.1)
    (Rep.of (R.frame.sectionRepresentation N.1))
    (R.frame.sectionModuleChart N.1)
    2 4 transported
    (R.frame.sectionRepresentation_schurCapacity_le_of_uniformDualEquiv
      (permutationFunctionRepresentation
        (ZMod 2) (naturalTopSubgroup kind) (Fin 16))
      e (DegreeTwoSixteenNaturalTopRealization.module_action_eq R) 4
      (permutationFunctionRepresentation_dual_uniform D.natural) N.1)

/-- Universal lift data for every realization of this natural top. -/
noncomputable def liftData
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoPairRelativeLiftData 16 p where
  profile := fun _ ↦ naturalProfile
  capacity := fun _ ↦ degreeTwoSixteenPairProfiles_capacity naturalProfile
    (by decide +kernel)
  envelope := D.envelope R hZmud lit

/-- Final natural-branch source produced by the common structural
converter. -/
noncomputable def source
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by norm_num) p) :=
  let lift := D.liftData R hZmud lit
  lift.rankTailSource (by norm_num)
    (degreeTwoSixteenPairRelativeNumerics lift)

end DegreeTwoSixteenNaturalFiniteRowData

/-- The serialized finite boundary has exactly two packages, one for each
natural literal top. -/
structure DegreeTwoSixteenNaturalFiniteCatalogueData : Type 1 where
  alternating : DegreeTwoSixteenNaturalFiniteRowData .alternating
  symmetric : DegreeTwoSixteenNaturalFiniteRowData .symmetric

namespace DegreeTwoSixteenNaturalFiniteCatalogueData

variable (D : DegreeTwoSixteenNaturalFiniteCatalogueData)

/-- Select one of the two explicit natural-top packages. -/
noncomputable def rowData (kind : DegreeTwoSixteenNaturalTop) :
    DegreeTwoSixteenNaturalFiniteRowData kind := by
  cases kind with
  | alternating => exact D.alternating
  | symmetric => exact D.symmetric

/-- Resolve either natural top by the same realization-independent
converter. -/
noncomputable def source
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (kind : DegreeTwoSixteenNaturalTop)
    (p : PreE7PairActionClass 16)
    (R : DegreeTwoSixteenNaturalTopRealization kind p) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by norm_num) p) :=
  (D.rowData kind).source R hZmud lit

end DegreeTwoSixteenNaturalFiniteCatalogueData
end DegreeTwoSixteenNaturalFiniteRows
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
