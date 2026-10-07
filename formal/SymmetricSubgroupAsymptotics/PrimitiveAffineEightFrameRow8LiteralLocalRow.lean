import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameOrderSixLocalCatalogue
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Selected eight-frame row 8: exact literal local catalogue

The executable point stabilizer has order six and its stored local action is
faithful.  Two explicit stabilizer elements have a commutator of order three,
so the stabilizer has no quotient of order three.  The stored order-six row is
therefore the complete eligible local catalogue.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8LiteralLocalRow

open PrimitiveAffineEightFrameRow8InducedBinding

local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow8TopCertificate.group

local instance inStabilizerDecidable (i : Fin 48) :
    Decidable (inStabilizer i) := by
  unfold inStabilizer
  infer_instance

local instance sourceStabilizerMembership (s : Source) :
    Decidable (s ∈ sourceStabilizer) :=
  inStabilizerDecidable s.index

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineEightFrameRow8TopCertificate.generators)

private theorem inStabilizer_iff_fixes_zero : ∀ s : Source,
    inStabilizer s.index ↔
      ((((PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv s :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  simp only [PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv_apply]
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃*
      MulAction.stabilizer LiteralAction (0 : Fin 8) where
  toFun s := ⟨PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv s.1,
    (inStabilizer_iff_fixes_zero s.1).mp s.2⟩
  invFun t :=
    ⟨PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv.symm t.1,
      (inStabilizer_iff_fixes_zero
        (PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv.symm t.1)).mpr
        (by
          rw [PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv.apply_symm_apply]
          exact t.2)⟩
  left_inv s := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv.symm_apply_apply s.1
  right_inv t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv.apply_symm_apply t.1
  map_mul' s t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv.map_mul s.1 t.1

def literalLocalMap :
    MulAction.stabilizer LiteralAction (0 : Fin 8) →*
      PrimitiveAffineEightFrameRow8InducedBinding.LocalTarget :=
  sourceLocalMap.comp sourceStabilizerEquivLiteral.symm.toMonoidHom

theorem literalLocalMap_surjective : Function.Surjective literalLocalMap :=
  sourceLocalMap_surjective.comp sourceStabilizerEquivLiteral.symm.surjective

noncomputable def literalLocalRow :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRow LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow8InducedBinding.LocalTarget
  literalLocalMap := literalLocalMap
  literalLocalMap_surjective := literalLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow8InducedBinding.localTarget_card

private def x : sourceStabilizer :=
  ⟨⟨1⟩, by native_decide +revert⟩

private def y : sourceStabilizer :=
  ⟨⟨2⟩, by native_decide +revert⟩

private theorem commutator_xy : x * y * x⁻¹ * y⁻¹ = y := by
  native_decide

private theorem orderOf_y : orderOf y = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · native_decide
  · native_decide

theorem source_no_order_three_quotient
    (L : Type) [Group L] [Finite L]
    (f : sourceStabilizer →* L)
    (_hf : Function.Surjective f)
    (hL : Nat.card L = 3) : False := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : IsCyclic L := isCyclic_of_prime_card hL
  letI : IsMulCommutative L := IsCyclic.isMulCommutative
  have hy : f y = 1 := by
    rw [← commutator_xy]
    simp only [map_mul, map_inv]
    rw [mul_comm' (f x) (f y)]
    simp
  have hyker : y ∈ f.ker := by
    simpa [MonoidHom.mem_ker] using hy
  have hdvd := f.ker.orderOf_dvd_natCard hyker
  have hkernel : Nat.card f.ker = 2 := by
    have hcard := f.ker.card_mul_index
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective _hf,
      Nat.card_congr Subgroup.topEquiv.toEquiv,
      PrimitiveAffineEightFrameRow8InducedBinding.sourceStabilizer_card,
      hL] at hcard
    omega
  rw [orderOf_y, hkernel] at hdvd
  norm_num at hdvd

theorem literal_no_order_three_quotient
    (L : Type) [Group L] [Finite L]
    (f : MulAction.stabilizer LiteralAction (0 : Fin 8) →* L)
    (hf : Function.Surjective f)
    (hL : Nat.card L = 3) : False :=
  source_no_order_three_quotient L
    (f.comp sourceStabilizerEquivLiteral.toMonoidHom)
    (hf.comp sourceStabilizerEquivLiteral.surjective) hL

theorem literalStabilizer_card :
    Nat.card (MulAction.stabilizer LiteralAction (0 : Fin 8)) = 6 := by
  rw [Nat.card_congr sourceStabilizerEquivLiteral.toEquiv.symm]
  exact PrimitiveAffineEightFrameRow8InducedBinding.sourceStabilizer_card

noncomputable def literalLocalCatalogue :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRowCatalogue LiteralAction :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRowCatalogue.singletonOfOrderSix
    LiteralAction literalLocalRow literalStabilizer_card
    literal_no_order_three_quotient
    PrimitiveAffineEightFrameRow8InducedBinding.localTarget_card

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8LiteralLocalRow

end
