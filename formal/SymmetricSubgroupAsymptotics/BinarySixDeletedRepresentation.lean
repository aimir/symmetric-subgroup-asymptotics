import SymmetricSubgroupAsymptotics.BinaryFourAffineImage

/-! The six-point deleted binary permutation module, in four coordinates.
Even vectors in F2^6 are considered modulo the constant vector. We choose
the representative with coordinate4 zero. Its first four coordinates
identify the quotient with F2^4; coordinate5 is their sum. The action laws
are proved through this normalization, without enumerating permutations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace BinarySixDeletedRepresentation

abbrev Vector := AffineModel.V 2 4
abbrev SixVector := Fin 6 → ZMod 2
abbrev LinearGroup := AffineModel.GLV 2 4

def constant (a : ZMod 2) : SixVector := fun _ => a

def encode (v : Vector) : SixVector :=
  ![v 0, v 1, v 2, v 3, 0, v 0 + v 1 + v 2 + v 3]

def decode (w : SixVector) : Vector :=
  ![w 0 + w 4, w 1 + w 4, w 2 + w 4, w 3 + w 4]

theorem encode_sum : ∀ v : Vector, ∑ i, encode v i = 0 := by decide +kernel
theorem decode_encode : ∀ v : Vector, decode (encode v) = v := by decide +kernel

/-- The chosen section changes an even vector by exactly one constant. -/
theorem encode_decode : ∀ w : SixVector, (∑ i, w i) = 0 →
    encode (decode w) = w + constant (w 4) := by
  decide +kernel

theorem encode_add (v w : Vector) : encode (v + w) = encode v + encode w := by
  revert v w
  decide +kernel

theorem encode_smul (a : ZMod 2) (v : Vector) : encode (a • v) = a • encode v := by
  revert a v
  decide +kernel

theorem decode_add (v w : SixVector) : decode (v + w) = decode v + decode w := by
  funext i
  fin_cases i <;> simp [decode, add_assoc, add_left_comm, add_comm]

theorem decode_smul (a : ZMod 2) (v : SixVector) : decode (a • v) = a • decode v := by
  funext i
  fin_cases i <;> simp [decode, mul_add]

theorem decode_constant (a : ZMod 2) : decode (constant a) = 0 := by
  revert a
  decide +kernel

def permute (σ : Equiv.Perm (Fin 6)) (w : SixVector) : SixVector :=
  fun i => w (σ.symm i)

theorem permute_sum (σ : Equiv.Perm (Fin 6)) (w : SixVector) :
    (∑ i, permute σ w i) = ∑ i, w i := Equiv.sum_comp σ.symm w

theorem permute_add (σ : Equiv.Perm (Fin 6)) (v w : SixVector) :
    permute σ (v + w) = permute σ v + permute σ w := rfl

theorem permute_smul (σ : Equiv.Perm (Fin 6)) (a : ZMod 2) (w : SixVector) :
    permute σ (a • w) = a • permute σ w := rfl

theorem permute_constant (σ : Equiv.Perm (Fin 6)) (a : ZMod 2) :
    permute σ (constant a) = constant a := rfl

theorem permute_mul (σ τ : Equiv.Perm (Fin 6)) (w : SixVector) :
    permute (σ * τ) w = permute σ (permute τ w) := rfl

def action (σ : Equiv.Perm (Fin 6)) (v : Vector) : Vector :=
  decode (permute σ (encode v))

theorem action_one (v : Vector) : action 1 v = v := decode_encode v

theorem action_mul (σ τ : Equiv.Perm (Fin 6)) (v : Vector) :
    action (σ * τ) v = action σ (action τ v) := by
  change decode (permute (σ * τ) (encode v)) =
    decode (permute σ (encode (decode (permute τ (encode v)))))
  rw [encode_decode _ (by rw [permute_sum, encode_sum]),
    permute_add, decode_add, permute_constant, decode_constant, add_zero, ← permute_mul]

def linear (σ : Equiv.Perm (Fin 6)) : LinearGroup where
  toFun := action σ
  invFun := action σ⁻¹
  left_inv := by intro v; rw [← action_mul, inv_mul_cancel, action_one]
  right_inv := by intro v; rw [← action_mul, mul_inv_cancel, action_one]
  map_add' := by intro v w; simp only [action, encode_add, permute_add, decode_add]
  map_smul' := by
    intro a v
    simp only [action, encode_smul, permute_smul, decode_smul, RingHom.id_apply]

def hom : Equiv.Perm (Fin 6) →* LinearGroup where
  toFun := linear
  map_one' := by apply LinearEquiv.ext; exact action_one
  map_mul' := by intro σ τ; apply LinearEquiv.ext; exact action_mul σ τ

/-- A concrete change of four-bit basis in the original target space. -/
def conjugateHom (e : LinearGroup) : Equiv.Perm (Fin 6) →* LinearGroup :=
  (MulAut.conj e).toMonoidHom.comp hom

def alpha : Equiv.Perm (Fin 6) := Fin.cycleRange 4
def beta16 : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 2 4 * Equiv.swap 3 5
def beta17 : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 1 * Equiv.swap 1 3) * (Equiv.swap 2 4 * Equiv.swap 4 5)

theorem hom_alpha : hom alpha =
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.cycle⁻¹ := by
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

end BinarySixDeletedRepresentation
end SymmetricSubgroupAsymptotics

end
