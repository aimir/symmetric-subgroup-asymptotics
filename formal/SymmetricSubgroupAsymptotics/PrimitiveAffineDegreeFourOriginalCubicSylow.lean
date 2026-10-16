import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalKleinCore
import SymmetricSubgroupAsymptotics.BinaryKernelCubicSylow
import SymmetricSubgroupAsymptotics.SylowActualNormalizerLift

/-! Exact original Sylow and normalizer inputs for the physical cubic
gauge, through an actual canonical chart of U/E. The original translation
kernel is identified literally, including for nonsplit extensions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    {C : Type} [Group C] (e : DegreeFourComplementQuotient block P ≃* C)

def degreeFourPhysicalCanonicalMap : preE7NonPairAction w U →* C :=
  e.toMonoidHom.comp (QuotientGroup.mk' (E block P))

theorem degreeFourPhysicalCanonicalMap_surjective :
    Function.Surjective (degreeFourPhysicalCanonicalMap block P e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective (E block P))

theorem degreeFourPhysicalCanonicalMap_ker :
    (degreeFourPhysicalCanonicalMap block P e).ker = E block P := by
  ext g
  change e (QuotientGroup.mk' (E block P) g) = 1 ↔ g ∈ E block P
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff (N := E block P) g).mp
    apply e.injective
    exact h.trans e.map_one.symm
  · intro h
    have hq : QuotientGroup.mk' (E block P) g = 1 :=
      (QuotientGroup.eq_one_iff (N := E block P) g).mpr h
    exact (congrArg e hq).trans e.map_one

theorem degreeFourPhysicalCanonicalMap_ker_binary (hr : Nat.card block.Fibre = 4) :
    IsPGroup 2 (degreeFourPhysicalCanonicalMap block P e).ker := by
  rw [degreeFourPhysicalCanonicalMap_ker]
  exact degreeFour_translationIntersection_isPGroup block P hr

local instance originalCubicSylowPrimeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem degreeFourOriginalCubicSylow_injective (hr : Nat.card block.Fibre = 4)
    (S : Sylow 3 (preE7NonPairAction w U)) :
    Function.Injective ((degreeFourPhysicalCanonicalMap block P e).comp
      (S : Subgroup (preE7NonPairAction w U)).subtype) :=
  BinaryKernelCubicSylow.restriction_injective
    (degreeFourPhysicalCanonicalMap block P e)
    (degreeFourPhysicalCanonicalMap_ker_binary block P e hr) S

include P e in
theorem degreeFourOriginalCubicSylow_card (hr : Nat.card block.Fibre = 4)
    (hcard : Nat.card C = 12 ∨ Nat.card C = 24)
    (S : Sylow 3 (preE7NonPairAction w U)) : Nat.card S = 3 :=
  BinaryKernelCubicSylow.card_three
    (degreeFourPhysicalCanonicalMap block P e)
    (degreeFourPhysicalCanonicalMap_surjective block P e)
    (degreeFourPhysicalCanonicalMap_ker_binary block P e hr) S hcard

theorem degreeFourOriginalCubicNormalizer_lift
    (S : Sylow 3 (preE7NonPairAction w U)) (c : C)
    (hc : c ∈ Subgroup.normalizer
      ((S : Subgroup (preE7NonPairAction w U)).map
        (degreeFourPhysicalCanonicalMap block P e) : Set C)) :
    ∃ g : preE7NonPairAction w U,
      g ∈ Subgroup.normalizer (S : Set (preE7NonPairAction w U)) ∧
        degreeFourPhysicalCanonicalMap block P e g = c :=
  SylowActualNormalizerLift.exists_lift
    (degreeFourPhysicalCanonicalMap block P e)
    (degreeFourPhysicalCanonicalMap_surjective block P e) S c hc

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
