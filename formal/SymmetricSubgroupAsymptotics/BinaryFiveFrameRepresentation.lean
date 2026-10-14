import SymmetricSubgroupAsymptotics.BinaryFourAffineImage
import Mathlib.LinearAlgebra.Pi

/-! The deleted five-point binary permutation representation in the
original four-bit coordinates. The ordered frame is [1,15,8,4,2].
The permutation homomorphism is proved symbolically through the even-sum
subspace; finite checks concern only vectors and individual point maps. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace BinaryFiveFrameRepresentation

abbrev Vector := AffineModel.V 2 4
abbrev FiveVector := Fin 5 → ZMod 2
abbrev LinearGroup := AffineModel.GLV 2 4

def evenSpace : Submodule (ZMod 2) FiveVector where
  carrier := {v | ∑ i, v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ i, (x i + y i) = 0
    rw [Finset.sum_add_distrib, hx, hy, zero_add]
  smul_mem' := by
    intro a x hx
    change ∑ i, a * x i = 0
    rw [← Finset.mul_sum, hx, mul_zero]

def encode (v : Vector) : FiveVector :=
  ![v 1 + v 2 + v 3, v 0 + v 1 + v 2 + v 3,
    v 0 + v 1 + v 2, v 0 + v 1 + v 3, v 0 + v 2 + v 3]

def decode (w : FiveVector) : Vector :=
  ![w 0 + w 1, w 1 + w 4, w 1 + w 3, w 1 + w 2]

theorem encode_sum : ∀ v : Vector, ∑ i, encode v i = 0 := by decide +kernel
theorem decode_encode : ∀ v : Vector, decode (encode v) = v := by decide +kernel
theorem encode_decode : ∀ w : FiveVector, (∑ i, w i) = 0 → encode (decode w) = w := by
  decide +kernel

def chart : Vector ≃ₗ[ZMod 2] evenSpace where
  toFun v := ⟨encode v, encode_sum v⟩
  invFun w := decode w.1
  left_inv := decode_encode
  right_inv := by
    intro w
    apply Subtype.ext
    exact encode_decode w.1 w.2
  map_add' := by
    intro x y
    apply Subtype.ext
    change encode (x + y) = encode x + encode y
    revert x y
    decide +kernel
  map_smul' := by
    intro a x
    apply Subtype.ext
    change encode (a • x) = a • encode x
    revert a x
    decide +kernel

def permLinear (σ : Equiv.Perm (Fin 5)) : evenSpace ≃ₗ[ZMod 2] evenSpace where
  toFun v := ⟨fun i => v.1 (σ.symm i), by
    change (∑ i, v.1 (σ.symm i)) = 0
    rw [Equiv.sum_comp]
    exact v.2⟩
  invFun v := ⟨fun i => v.1 (σ i), by
    change (∑ i, v.1 (σ i)) = 0
    rw [Equiv.sum_comp]
    exact v.2⟩
  left_inv := by
    intro v
    apply Subtype.ext
    funext i
    exact congrArg v.1 (σ.symm_apply_apply i)
  right_inv := by
    intro v
    apply Subtype.ext
    funext i
    exact congrArg v.1 (σ.apply_symm_apply i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def hom : Equiv.Perm (Fin 5) →* LinearGroup where
  toFun σ := (chart.trans (permLinear σ)).trans chart.symm
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change chart.symm (permLinear 1 (chart v)) = v
    change chart.symm (chart v) = v
    exact chart.symm_apply_apply v
  map_mul' := by
    intro σ τ
    apply LinearEquiv.ext
    intro v
    change chart.symm (permLinear (σ * τ) (chart v)) =
      chart.symm (permLinear σ (chart (chart.symm (permLinear τ (chart v)))))
    rw [chart.apply_symm_apply]
    apply congrArg chart.symm
    apply Subtype.ext
    funext i
    rfl

def cycle : Equiv.Perm (Fin 5) := finRotate 5
def transposition : Equiv.Perm (Fin 5) := Equiv.swap 0 1
def doubleTransposition : Equiv.Perm (Fin 5) := Equiv.swap 0 3 * Equiv.swap 1 4

theorem hom_cycle : hom cycle =
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.cycle := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem hom_transposition_original :
    BinaryFourAffineImage.linearPerm (hom transposition) =
      DegreeTwoPrimitiveSixteenInterfaces.row18Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem hom_doubleTransposition_original :
    BinaryFourAffineImage.linearPerm (hom doubleTransposition) =
      DegreeTwoPrimitiveSixteenInterfaces.row19Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

end BinaryFiveFrameRepresentation
end SymmetricSubgroupAsymptotics

end
