import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameAbstractS4LocalCatalogue

/-!
# Selected eight-frame row 9: exact literal local catalogue

The point stabilizer of the order-192 top restricts faithfully to the second
four-point block, giving an explicit copy of `S₄`.  The stored local kernel is
the natural Klein four subgroup under that restriction.  The generic abstract
`S₄` theorem therefore makes row 9 the complete eligible local catalogue.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9LiteralLocalRow

open PrimitiveAffineEightFrameRow9InducedBinding

local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow9TopCertificate.group

local instance inStabilizerDecidable (i : Fin 192) :
    Decidable (inStabilizer i) := by
  unfold inStabilizer
  infer_instance

local instance sourceStabilizerMembership (s : Source) :
    Decidable (s ∈ sourceStabilizer) :=
  inStabilizerDecidable s.index

/-- The literal order-192 top. -/
abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineEightFrameRow9TopCertificate.generators)

private theorem inStabilizer_iff_fixes_zero : ∀ s : Source,
    inStabilizer s.index ↔
      ((((PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv s :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  simp only [PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv_apply]
  native_decide +revert

/-- The emitted Cayley stabilizer is exactly the stabilizer of zero in the
literal top. -/
def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃*
      MulAction.stabilizer LiteralAction (0 : Fin 8) where
  toFun s := ⟨PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv s.1,
    (inStabilizer_iff_fixes_zero s.1).mp s.2⟩
  invFun t :=
    ⟨PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv.symm t.1,
      (inStabilizer_iff_fixes_zero
        (PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv.symm t.1)).mpr
        (by
          rw [PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv.apply_symm_apply]
          exact t.2)⟩
  left_inv s := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv.symm_apply_apply s.1
  right_inv t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv.apply_symm_apply t.1
  map_mul' s t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv.map_mul s.1 t.1

private def upperPoint (q : Fin 4) : Fin 8 :=
  ⟨q.val + 4, by omega⟩

private def secondBlockValue (h : sourceStabilizer) (q : Fin 4) : ℕ :=
  (PrimitiveAffineEightFrameRow9TopCertificate.certificate.toCayley.elements
    h.1.index (upperPoint q)).val - 4

private theorem secondBlockValue_lt : ∀ h : sourceStabilizer, ∀ q : Fin 4,
    secondBlockValue h q < 4 := by
  native_decide +revert

private def secondBlockForward (h : sourceStabilizer) (q : Fin 4) : Fin 4 :=
  ⟨secondBlockValue h q, secondBlockValue_lt h q⟩

/-- Restriction of one stabilizer element to the second four-point block. -/
def secondBlockPermutation (h : sourceStabilizer) : Equiv.Perm (Fin 4) where
  toFun := secondBlockForward h
  invFun := secondBlockForward h⁻¹
  left_inv := by native_decide +revert
  right_inv := by native_decide +revert

private theorem secondBlockPermutation_one :
    secondBlockPermutation 1 = 1 := by native_decide

private theorem secondBlockPermutation_mul : ∀ x y : sourceStabilizer,
    secondBlockPermutation (x * y) =
      secondBlockPermutation x * secondBlockPermutation y := by
  native_decide +revert

def sourceToS4 : sourceStabilizer →* Equiv.Perm (Fin 4) where
  toFun := secondBlockPermutation
  map_one' := secondBlockPermutation_one
  map_mul' := secondBlockPermutation_mul

private theorem sourceToS4_bijective : Function.Bijective sourceToS4 := by
  native_decide

/-- The checked point stabilizer identification with natural `S₄`. -/
def sourceStabilizerEquivS4 :
    sourceStabilizer ≃* Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective sourceToS4 sourceToS4_bijective

def literalLocalMap :
    MulAction.stabilizer LiteralAction (0 : Fin 8) →*
      PrimitiveAffineEightFrameRow9InducedBinding.LocalTarget :=
  sourceLocalMap.comp sourceStabilizerEquivLiteral.symm.toMonoidHom

theorem literalLocalMap_surjective : Function.Surjective literalLocalMap :=
  sourceLocalMap_surjective.comp sourceStabilizerEquivLiteral.symm.surjective

noncomputable def literalLocalRow :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRow LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow9InducedBinding.LocalTarget
  literalLocalMap := literalLocalMap
  literalLocalMap_surjective := literalLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow9InducedBinding.localTarget_card

private theorem sourceLocalMap_kernel :
    sourceLocalMap.ker =
      NaturalS4.klein.comap sourceToS4 := by
  ext h
  simp only [MonoidHom.mem_ker, Subgroup.mem_comap]
  have hraw : rawLocalMap h = 1 ↔ sourceToS4 h ∈ NaturalS4.klein := by
    native_decide +revert
  constructor
  · intro hh
    apply hraw.mp
    exact congrArg Subtype.val hh
  · intro hh
    apply Subtype.ext
    exact hraw.mpr hh

/-- The literal stabilizer identified with natural `S₄`. -/
def literalStabilizerEquivS4 :
    MulAction.stabilizer LiteralAction (0 : Fin 8) ≃*
      Equiv.Perm (Fin 4) :=
  sourceStabilizerEquivLiteral.symm.trans sourceStabilizerEquivS4

private theorem literalLocalMap_kernel :
    literalLocalMap.ker =
      NaturalS4.klein.comap literalStabilizerEquivS4.toMonoidHom := by
  ext x
  change sourceLocalMap (sourceStabilizerEquivLiteral.symm x) = 1 ↔
    sourceToS4 (sourceStabilizerEquivLiteral.symm x) ∈ NaturalS4.klein
  have h := SetLike.ext_iff.mp sourceLocalMap_kernel
    (sourceStabilizerEquivLiteral.symm x)
  exact h

/-- Row 9 is the complete local catalogue of its literal top. -/
noncomputable def literalLocalCatalogue :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRowCatalogue LiteralAction :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRowCatalogue.singletonOfAbstractS4
    LiteralAction literalLocalRow literalStabilizerEquivS4
      literalLocalMap_kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9LiteralLocalRow

end
