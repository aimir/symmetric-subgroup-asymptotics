import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonzeroOrbitHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonzeroRank
import SymmetricSubgroupAsymptotics.BinaryTopNormalizerOrbitHead

/-! The original four-by-four branch with nonzero ternary core satisfies
the ten-slot frame inequality. Binary block tops use a lifted normalizer
element; nonbinary block tops use a nine-point orbit of the same original
Sylow. The normal subgroup and external point-stabilizer epimorphism stay
arbitrary and unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- The binary-top head estimate needs no hypothesis on the ternary core. -/
theorem degreeFourFourBlockBinaryTop_original_head_le_four
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    (hTop : IsPGroup 2 block.Top) (x : Fin w)
    (f : MulAction.stabilizer (preE7NonPairAction w U) x →* L)
    (hf : Function.Surjective f) (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (preE7NonPairAction w U) x).subtype
        (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) (preE7NonPairAction w U) (ZMod 2))) ≤ 4 := by
  letI : Nontrivial block.Points :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  have hw : Nat.card (Fin w) = 16 := by
    have h := block.degree_product
    rw [hr, hs] at h
    exact h.symm
  exact BinaryTopNormalizerOrbitHead.head_le_four_on_points x hw
    block.topMap.rangeRestrict block.topMap.rangeRestrict_surjective hTop
    (fun _ _ => rfl) block.map block.map_equivariant f hf rho hL hdim hrho B

/-- All block-top cases are covered internally. The only non-geometric
inputs are the already explicit published inputs of the retained-socle
rank theorem. No local rank or frame-capacity certificate is assumed. -/
theorem degreeFourNonzeroFourBlock_original_sum_le_ten
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (x : Fin w) (f : MulAction.stabilizer (preE7NonPairAction w U) x →* L)
    (hf : Function.Surjective f) (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (N : Subgroup (preE7NonPairAction w U)) [N.Normal]
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (preE7NonPairAction w U) x).subtype
        (rho.comp f))) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) (preE7NonPairAction w U) (ZMod 2))) ≤ 10 := by
  have hn := degreeFourFourBlockNonzero_binary_relative_head_le_four block P
    hMN hClifford hTraceyPerm hr hs hD N
  by_cases hTop : IsPGroup 2 block.Top
  · have hb := degreeFourFourBlockBinaryTop_original_head_le_four block
      hr hs hTop x f hf rho hL hdim hrho B
    omega
  · have hb := degreeFourNonzeroFourBlock_original_head_le_six block P
      hr hs hD hTop x f hf rho hL hdim hrho B
    omega

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
