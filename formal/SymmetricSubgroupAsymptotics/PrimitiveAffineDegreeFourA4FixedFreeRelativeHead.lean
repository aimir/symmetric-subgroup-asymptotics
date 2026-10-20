import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourFixedFreeTopHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourA4OriginalGroupChart
import SymmetricSubgroupAsymptotics.BinaryFourA4NormalRelativeHead
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-! The actual A4 branch of the dynamic sixteen-point frame has zero
relative binary head when its unchanged translation action is fixed-free. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
local instance primitiveAffineDegreeFourA4FixedFreeRelativeHead_localFact1 : Fact (Nat.Prime 2) := ⟨by decide⟩

namespace DegreeFourA4OriginalPointChart
variable (C : DegreeFourA4OriginalPointChart block)

include C

theorem original_fixedFree_relative_head_zero
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (g : preE7NonPairAction w U)
    (hg : (QuotientGroup.mk' (E block P) g) ^ 3 = 1)
    (hfixed : ∀ v : (elementaryChart block P).V,
      (elementaryChart block P).quotientRepresentation.ρ
        (QuotientGroup.mk' (E block P) g) v = v → v = 0)
    (N : Subgroup (preE7NonPairAction w U)) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) = 0 := by
  let e := groupEquiv (block := block) (P := P) (C := C) hr hD
  let A := normalChainQuotient (E block P) N
  let M := A.map e.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have heq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 A) :=
    (relativeCharacterAmbientCongr 2 e A M rfl).finrank_eq
  have hz := BinaryFourA4NormalRelativeHead.normal_relative_head_zero M
  have h := degreeFour_fixedFree_relative_head_le_actual_top_image
    block P (degreeFour_profilePrime_eq_two block P hr) g hg hfixed N
  change Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 A) at h
  rw [← heq, hz] at h
  exact Nat.eq_zero_of_le_zero h

end DegreeFourA4OriginalPointChart
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
