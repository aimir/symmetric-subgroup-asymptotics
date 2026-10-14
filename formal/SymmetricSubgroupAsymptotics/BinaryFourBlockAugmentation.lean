import SymmetricSubgroupAsymptotics.BinaryFourAffineImage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces

/-! Explicit coordinates for the common augmentation translation module
of the zero16 rows9 and11. A fixed local gauge and change of origin make
the two Klein block generators pure block permutations. All identities
below concern displayed binary linear formulas and the original points. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourBlockAugmentation

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Scalar := ZMod 2
abbrev Local := Fin 2 → Scalar
abbrev Module := Fin 4 → Local
abbrev Coordinates := Fin 6 → Scalar

def localCycle : Local ≃ₗ[Scalar] Local where
  toFun x := ![x 0 + x 1, x 0]
  invFun x := ![x 1, x 0 + x 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def gauge (b : Fin 4) : Local ≃ₗ[Scalar] Local :=
  ![1, localCycle, localCycle⁻¹, localCycle] b

def localOfMask (n : ℕ) : Local := binaryVectorOfMask 2 n

/-- The origin shift is in the gauged coordinates. -/
def shift (b : Fin 4) : Local :=
  ![localOfMask 1, localOfMask 3, 0, localOfMask 3] b

def pointEquiv : (Fin 4 × Local) ≃ Fin 16 where
  toFun x := Fin.ofNat 16 (4 * x.1.val + binaryVectorMask (gauge x.1 (x.2 + shift x.1)))
  invFun i :=
    let b : Fin 4 := ⟨i.val / 4, by omega⟩
    (b, (gauge b).symm (localOfMask (i.val % 4)) + shift b)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def fiberTranslation : Multiplicative Module →* Equiv.Perm (Fin 4 × Local) where
  toFun w :=
    { toFun x := (x.1, w.toAdd x.1 + x.2)
      invFun x := (x.1, -w.toAdd x.1 + x.2)
      left_inv x := by simp
      right_inv x := by simp }
  map_one' := by apply Equiv.ext; intro x; simp
  map_mul' w z := by apply Equiv.ext; intro x; simp [add_assoc]

def translation : Multiplicative Module →* Equiv.Perm (Fin 16) :=
  pointEquiv.permCongrHom.toMonoidHom.comp fiberTranslation

theorem translation_injective : Function.Injective translation := by
  intro w z h
  have he := pointEquiv.permCongrHom.injective h
  apply Multiplicative.toAdd.injective
  funext b
  have hh := congrArg (fun p : Equiv.Perm (Fin 4 × Local) => (p (b, 0)).2) he
  change w.toAdd b + 0 = z.toAdd b + 0 at hh
  simpa only [add_zero] using hh

/-- Two diagonal coordinates followed by three cyclic translates of t
and the extra row11 vector. -/
def decode (x : Coordinates) : Module :=
  ![![x 0 + x 3 + x 4, x 1 + x 2 + x 4],
    ![x 0, x 1 + x 2],
    ![x 0 + x 3 + x 5, x 1 + x 5],
    ![x 0 + x 4 + x 5, x 1 + x 4 + x 5]]

def encode (w : Module) : Coordinates :=
  ![w 1 0,
    w 1 0 + w 3 0 + w 3 1,
    w 1 1 + w 1 0 + w 3 0 + w 3 1,
    w 2 0 + w 2 1 + w 3 0 + w 3 1,
    w 3 1 + w 2 1,
    w 2 1 + w 1 0 + w 3 0 + w 3 1]

theorem encode_decode (x : Coordinates) : encode (decode x) = x := by
  revert x
  decide +kernel

theorem decode_add (x y : Coordinates) : decode (x + y) = decode x + decode y := by
  ext b i
  fin_cases b <;> fin_cases i <;> simp [decode] <;> ring

theorem decode_zero : decode 0 = 0 := by decide +kernel

def decodeHom : Multiplicative Coordinates →* Multiplicative Module where
  toFun x := Multiplicative.ofAdd (decode x.toAdd)
  map_one' := congrArg Multiplicative.ofAdd decode_zero
  map_mul' x y := congrArg Multiplicative.ofAdd (decode_add x.toAdd y.toAdd)

def translations : Multiplicative Coordinates →* Equiv.Perm (Fin 16) :=
  translation.comp decodeHom

theorem translations_injective : Function.Injective translations := by
  intro x y h
  apply Multiplicative.toAdd.injective
  have hd := congrArg Multiplicative.toAdd (translation_injective h)
  exact (encode_decode x.toAdd).symm.trans ((congrArg encode hd).trans (encode_decode y.toAdd))

def u : Coordinates ≃ₗ[Scalar] Coordinates where
  toFun x := ![x 0 + x 4 + x 5, x 1 + x 2 + x 4 + x 5, x 2, x 3, x 4, x 5]
  invFun x := ![x 0 + x 4 + x 5, x 1 + x 2 + x 4 + x 5, x 2, x 3, x 4, x 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by decide +kernel

def v : Coordinates ≃ₗ[Scalar] Coordinates where
  toFun x := ![x 0 + x 3 + x 4, x 1 + x 4, x 2, x 3, x 4, x 5]
  invFun x := ![x 0 + x 3 + x 4, x 1 + x 4, x 2, x 3, x 4, x 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by decide +kernel

def c : Coordinates ≃ₗ[Scalar] Coordinates where
  toFun x := ![x 0 + x 1, x 0 + x 5, x 4, x 2 + x 5, x 3 + x 5, x 5]
  invFun x := ![x 1 + x 5, x 0 + x 1 + x 5, x 3 + x 5, x 4 + x 5, x 2, x 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by decide +kernel

def blockU : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
def blockV : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
def blockC : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3

def uPerm : Equiv.Perm (Fin 16) :=
  pointEquiv.permCongr (blockU.prodCongr (Equiv.refl Local))
def vPerm : Equiv.Perm (Fin 16) :=
  pointEquiv.permCongr (blockV.prodCongr (Equiv.refl Local))
def cPerm : Equiv.Perm (Fin 16) :=
  pointEquiv.permCongr (blockC.prodCongr localCycle.toEquiv)

def basisVector (i : Fin 6) : Coordinates := Pi.single i 1
def correction : Coordinates := ![1, 1, 0, 1, 0, 0]

theorem original_u : uPerm = DegreeTwoZeroSixteenInterfaces.row9Generators 1 := by
  apply Equiv.ext; intro i; revert i; decide +kernel
theorem original_v : vPerm = DegreeTwoZeroSixteenInterfaces.row9Generators 2 := by
  apply Equiv.ext; intro i; revert i; decide +kernel
theorem original_t : translations (Multiplicative.ofAdd (basisVector 2)) =
    DegreeTwoZeroSixteenInterfaces.row9Generators 3 := by
  apply Equiv.ext; intro i; revert i; decide +kernel
theorem original_c : translations (Multiplicative.ofAdd correction) * cPerm =
    DegreeTwoZeroSixteenInterfaces.row9Generators 0 := by
  apply Equiv.ext; intro i; revert i; decide +kernel
theorem original_extra : translations (Multiplicative.ofAdd (basisVector 5)) =
    DegreeTwoZeroSixteenInterfaces.row11Generators 4 := by
  apply Equiv.ext; intro i; revert i; decide +kernel

theorem shared_generators (i : Fin 4) :
    DegreeTwoZeroSixteenInterfaces.row11Generators i.castSucc =
      DegreeTwoZeroSixteenInterfaces.row9Generators i := by
  fin_cases i <;> rfl

theorem conjugate_u (x : Coordinates) :
    uPerm * translations (Multiplicative.ofAdd x) * uPerm⁻¹ =
      translations (Multiplicative.ofAdd (u x)) := by
  apply Equiv.ext; intro i
  fin_cases i <;> revert x <;> decide +kernel

theorem conjugate_v (x : Coordinates) :
    vPerm * translations (Multiplicative.ofAdd x) * vPerm⁻¹ =
      translations (Multiplicative.ofAdd (v x)) := by
  apply Equiv.ext; intro i
  fin_cases i <;> revert x <;> decide +kernel

theorem conjugate_c (x : Coordinates) :
    cPerm * translations (Multiplicative.ofAdd x) * cPerm⁻¹ =
      translations (Multiplicative.ofAdd (c x)) := by
  apply Equiv.ext; intro i
  fin_cases i <;> revert x <;> decide +kernel

end BinaryFourBlockAugmentation
end SymmetricSubgroupAsymptotics

end
