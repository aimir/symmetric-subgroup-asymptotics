import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonzeroCore
import SymmetricSubgroupAsymptotics.PrimeSectionalPowerKernel

/-! The exact linear quotient of a four-point affine block action has
binary sectional rank at most its number of blocks. The actual correlated
ternary kernel is discarded, and its actual signed image acts faithfully
on two points per block. This applies to both zero and nonzero cores. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

theorem degreeFourTernaryCore_isPGroup (hr : Nat.card block.Fibre = 4) :
    IsPGroup 3 (degreeFourTernaryCore block P) := by
  intro d
  refine ⟨1, ?_⟩
  apply degreeFourTernaryCoordinate_joint_injective block P
  funext i
  simp only [map_pow, map_one, pow_one]
  have h := pow_card_eq_one' (x := degreeFourTernaryCoordinate block P i d)
  rwa [degreeFourLocalBinarySign_ker_card block P hr] at h

/-- No replacement by the full ternary base is made. The rank estimate
uses precisely the kernel of the original signed-wreath homomorphism. -/
theorem degreeFourComplement_binary_sectional_rank
    (hr : Nat.card block.Fibre = 4) :
    PrimeSectionalRankBound 2 (DegreeFourComplementQuotient block P)
      (Nat.card block.Points) := by
  let Q := PermutationalWreathProduct (Multiplicative (ZMod 2))
    block.Top block.Points
  let X := Multiplicative (ZMod 2) × block.Points
  let f : DegreeFourComplementQuotient block P →* Q :=
    degreeFourSignedWreathMap block P
  letI : Finite Q := Finite.of_injective
    (PermutationalWreathProduct.toPerm
      (D := Multiplicative (ZMod 2)) (Q := block.Top)
      (I := block.Points) (Lambda := Multiplicative (ZMod 2)))
    PermutationalWreathProduct.toPerm_injective
  have hker : IsPGroup 3 f.ker := degreeFourTernaryCore_isPGroup block P hr
  have h := primeSectionalRankBound_of_power_kernel_permutation 2
    (X := X) 3 (by decide) f hker
  have hcard : Nat.card X / 2 = Nat.card block.Points := by
    change Nat.card (Multiplicative (ZMod 2) × block.Points) / 2 = _
    rw [Nat.card_prod]
    change (Nat.card (ZMod 2) * Nat.card block.Points) / 2 = _
    rw [Nat.card_zmod]
    omega
  exact hcard ▸ h

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
