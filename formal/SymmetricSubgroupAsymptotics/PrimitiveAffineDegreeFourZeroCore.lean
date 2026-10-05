import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonzeroCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryExceptionalLocal

/-!
# The zero ternary core in affine degree four

For an exact affine component of degree four, let `K` be the literal block
kernel after quotienting the binary translations, and let `D` be the kernel
of all local binary signs.  This file proves the structural implication used
by the zero-core branch of the manuscript:

`D = 1  ->  K = 1`.

The proof stays in the actual wreath embedding.  Vanishing of `D` makes
every element of `K` an involution.  Each coordinate image of `K` is normal
in the exact local `C3` or `S3`.  Its intersection with the local `C3` is
therefore trivial; normality then makes every coordinate centralize that
`C3`, and the checked local sign-kernel calculation forces the coordinate
itself to be trivial.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private theorem binary_mul_pow_two_local
    (x : Multiplicative (ZMod 2)) : x ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  exact ZModModule.char_nsmul_eq_zero 2 x.toAdd

/-- If the simultaneous local-sign kernel is trivial, every element of the
literal linear block kernel is an involution. -/
theorem degreeFourLinearBlockKernel_pow_two_eq_one_of_core_eq_bot
    (hD : degreeFourTernaryCore block P = ⊥)
    (k : binaryAffineLinearBlockKernel block P) :
    (k.1 : DegreeFourComplementQuotient block P) ^ 2 = 1 := by
  have hkD : (k.1 : DegreeFourComplementQuotient block P) ^ 2 ∈
      degreeFourTernaryCore block P := by
    apply MonoidHom.mem_ker.mpr
    change degreeFourSignedWreathMap block P (k.1 ^ 2) = 1
    rw [map_pow]
    apply PermutationalWreathProduct.ext
    · funext i
      rw [pow_two, PermutationalWreathProduct.mul_left]
      have hkright : (quotientEmbedding block P k.1).right = 1 :=
        MonoidHom.mem_ker.mp k.2
      simp only [degreeFourSignedWreathMap, MonoidHom.comp_apply,
        PermutationalWreathProduct.mapBase_left,
        PermutationalWreathProduct.mapBase_right, hkright, inv_one,
        one_smul, PermutationalWreathProduct.one_left, Pi.one_apply]
      rw [Pi.mul_apply]
      simpa only [pow_two] using binary_mul_pow_two_local _
    · have hkright :
          (degreeFourSignedWreathMap block P k.1).right = 1 := by
        exact MonoidHom.mem_ker.mp k.2
      change ((degreeFourSignedWreathMap block P k.1) ^ 2).right = 1
      rw [pow_two, PermutationalWreathProduct.mul_right, hkright, one_mul]
  rw [hD] at hkD
  exact Subgroup.mem_bot.mp hkD

/-- An element of the local sign kernel which is also an involution is
trivial, because that kernel has the checked order three. -/
theorem degreeFourSignKernel_eq_one_of_pow_two
    (hr : Nat.card block.Fibre = 4)
    (z : (degreeFourLocalBinarySign block P).ker)
    (hz2 : (z.1 : LocalQuotient block P) ^ 2 = 1) : z = 1 := by
  have hz3sub : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := z)
    rw [degreeFourLocalBinarySign_ker_card block P hr] at h
    exact h
  have hz3 : (z.1 : LocalQuotient block P) ^ 3 = 1 :=
    congrArg Subtype.val hz3sub
  apply Subtype.ext
  calc
    (z.1 : LocalQuotient block P) = 1 * z.1 := (one_mul _).symm
    _ = z.1 ^ 2 * z.1 := by rw [hz2]
    _ = z.1 ^ 3 := by group
    _ = 1 := hz3

/-- Every coordinate image of the zero-core linear block kernel vanishes. -/
theorem degreeFourLinearBlockKernelCoordinate_range_eq_bot_of_core_eq_bot
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (i : block.Points) :
    (binaryAffineLinearBlockKernelCoordinate block P i).range = ⊥ := by
  let K := binaryAffineLinearBlockKernel block P
  let C := binaryAffineLinearBlockKernelCoordinate block P i
  let R := C.range
  letI : R.Normal :=
    binaryAffineLinearBlockKernelCoordinate_range_normal block P i
  rw [eq_bot_iff]
  intro y hy
  apply Subgroup.mem_bot.mpr
  have hyR : y ∈ R := hy
  obtain ⟨k, hk⟩ := hy
  have hk2 := degreeFourLinearBlockKernel_pow_two_eq_one_of_core_eq_bot
    block P hD k
  have hy2 : (y : LocalQuotient block P) ^ 2 = 1 := by
    rw [← hk]
    have hk2sub : k ^ 2 = 1 := Subtype.ext hk2
    rw [← map_pow, hk2sub, map_one]
  have hcentral : ∀ z : (degreeFourLocalBinarySign block P).ker,
      Commute (y : LocalQuotient block P) z.1 := by
    intro z
    have hcR : ⁅z.1, (y : LocalQuotient block P)⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem
        ((inferInstance : R.Normal).conj_mem y hyR z.1)
        (R.inv_mem hyR)
    let c : R := ⟨⁅z.1, (y : LocalQuotient block P)⁆, hcR⟩
    have hc2 : (c.1 : LocalQuotient block P) ^ 2 = 1 := by
      obtain ⟨k', hk'⟩ := c.2
      rw [← hk']
      have hk2sub : k' ^ 2 = 1 := Subtype.ext
        (degreeFourLinearBlockKernel_pow_two_eq_one_of_core_eq_bot
          block P hD k')
      rw [← map_pow, hk2sub, map_one]
    have hcsign : c.1 ∈ (degreeFourLocalBinarySign block P).ker := by
      apply MonoidHom.mem_ker.mpr
      change degreeFourLocalBinarySign block P ⁅z.1, (y : LocalQuotient block P)⁆ = 1
      rw [map_commutatorElement]
      have hz : degreeFourLocalBinarySign block P z.1 = 1 := z.2
      rw [hz]
      simp
    let c' : (degreeFourLocalBinarySign block P).ker := ⟨c.1, hcsign⟩
    have hc' : c' = 1 := degreeFourSignKernel_eq_one_of_pow_two
      block P hr c' hc2
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (congrArg Subtype.val hc')).symm
  have hysign : y ∈ (degreeFourLocalBinarySign block P).ker :=
    degreeFourLocal_mem_signKernel_of_centralizes block P hr y hcentral
  let y' : (degreeFourLocalBinarySign block P).ker := ⟨y, hysign⟩
  exact congrArg Subtype.val
    (degreeFourSignKernel_eq_one_of_pow_two block P hr y' hy2)

/-- Zero ternary core forces the entire literal linear block kernel to
vanish, so the quotient after translations acts faithfully on the actual
set of blocks. -/
theorem degreeFourLinearBlockKernel_eq_bot_of_core_eq_bot
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    binaryAffineLinearBlockKernel block P = ⊥ := by
  let i : block.Points := Classical.choice (inferInstance : Nonempty block.Points)
  exact binaryAffineLinearBlockKernel_eq_bot_of_coordinate_range_eq_bot
    block P i
      (degreeFourLinearBlockKernelCoordinate_range_eq_bot_of_core_eq_bot
        block P hr hD i)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
