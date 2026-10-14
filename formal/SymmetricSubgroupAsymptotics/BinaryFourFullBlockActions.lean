import SymmetricSubgroupAsymptotics.BinaryFourFullBlockCoordinates

/-! The full block-translation module with its original A4 action.
The complement is the already checked Klein-by-three model. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation SemidirectProduct

def fullKleinFun (p : Klein) (x : FullCoordinates) : FullCoordinates :=
  ![x 0 + p.toAdd 0 * (x 4 + x 5) + p.toAdd 1 * (x 3 + x 4 + x 6) +
      p.toAdd 0 * p.toAdd 1 * x 6,
    x 1 + p.toAdd 0 * (x 2 + x 4 + x 5) + p.toAdd 1 * (x 4 + x 6) +
      p.toAdd 0 * p.toAdd 1 * x 7,
    x 2 + p.toAdd 1 * (x 6 + x 7),
    x 3 + p.toAdd 0 * (x 6 + x 7),
    x 4 + p.toAdd 0 * x 7,
    x 5 + p.toAdd 0 * x 7 + p.toAdd 1 * x 6, x 6, x 7]

theorem fullKleinFun_involutive (p : Klein) : Function.Involutive (fullKleinFun p) := by
  intro x
  ext i
  fin_cases i <;> simp [fullKleinFun] <;> ring_nf <;>
    simp only [show (2 : Scalar) = 0 from by decide +kernel,
      show (4 : Scalar) = 0 from by decide +kernel,
      mul_zero, zero_add, add_zero]

theorem fullKleinFun_add (p : Klein) (x y : FullCoordinates) :
    fullKleinFun p (x + y) = fullKleinFun p x + fullKleinFun p y := by
  ext i
  fin_cases i <;> simp [fullKleinFun] <;> ring

theorem fullKleinFun_smul (p : Klein) (a : Scalar) (x : FullCoordinates) :
    fullKleinFun p (a • x) = a • fullKleinFun p x := by
  ext i
  fin_cases i <;> simp [fullKleinFun] <;> ring

def fullKlein (p : Klein) : FullCoordinates ≃ₗ[Scalar] FullCoordinates where
  toFun := fullKleinFun p
  invFun := fullKleinFun p
  left_inv := fullKleinFun_involutive p
  right_inv := fullKleinFun_involutive p
  map_add' := fullKleinFun_add p
  map_smul' := fullKleinFun_smul p

def fullKleinHom : Klein →* (FullCoordinates ≃ₗ[Scalar] FullCoordinates) where
  toFun := fullKlein
  map_one' := by
    apply linearEquiv_ext_basis
    intro i
    revert i
    decide +kernel
  map_mul' p q := by
    apply linearEquiv_ext_basis
    intro i
    revert p q i
    decide +kernel

def fullTernary : Ternary →* (FullCoordinates ≃ₗ[Scalar] FullCoordinates) :=
  powersHom 3 fullC fullC_cube

theorem fullCompatibility (z : Ternary) :
    fullKleinHom.comp (kleinCyclicAction z).toMonoidHom =
      (MulAut.conj (fullTernary z)).toMonoidHom.comp fullKleinHom := by
  apply MonoidHom.ext
  intro p
  apply linearEquiv_ext_basis
  intro i
  revert z p i
  decide +kernel

def fullComplementLinear : Complement →* (FullCoordinates ≃ₗ[Scalar] FullCoordinates) :=
  SemidirectProduct.lift fullKleinHom fullTernary fullCompatibility

def fullAction : Complement →* MulAut (Multiplicative FullCoordinates) where
  toFun r := (fullComplementLinear r).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro x
    exact congrArg (fun f : FullCoordinates ≃ₗ[Scalar] FullCoordinates =>
      Multiplicative.ofAdd (f x.toAdd)) fullComplementLinear.map_one
  map_mul' r s := by
    apply MulEquiv.ext
    intro x
    exact congrArg (fun f : FullCoordinates ≃ₗ[Scalar] FullCoordinates =>
      Multiplicative.ofAdd (f x.toAdd)) (fullComplementLinear.map_mul r s)

abbrev Ambient := Multiplicative FullCoordinates ⋊[fullAction] Complement

instance : Finite Ambient :=
  Finite.of_equiv (Multiplicative FullCoordinates × Complement)
    SemidirectProduct.equivProd.symm

theorem fullLinear_u : fullComplementLinear uElement = fullU := by
  apply linearEquiv_ext_basis
  intro i
  revert i
  decide +kernel

theorem fullLinear_v : fullComplementLinear vElement = fullV := by
  apply linearEquiv_ext_basis
  intro i
  revert i
  decide +kernel

theorem fullLinear_c : fullComplementLinear cElement = fullC := by
  apply linearEquiv_ext_basis
  intro i
  revert i
  decide +kernel

theorem fullKlein_formula (p : Klein) :
    fullU ^ (p.toAdd 0).val * fullV ^ (p.toAdd 1).val = fullKlein p := by
  apply linearEquiv_ext_basis
  intro i
  revert p i
  decide +kernel

theorem fullKlein_augmentation (p : Klein) (x : FullCoordinates) :
    augmentation (fullKlein p x) = augmentation x := rfl

theorem fullC_augmentation (x : FullCoordinates) :
    augmentation (fullC x) = localCycle (augmentation x) := rfl

theorem fullC_fifth (x : FullCoordinates) : fullC x 5 = x 5 := rfl

theorem fullTernary_augmentation (z : Ternary) (x : FullCoordinates) :
    augmentation (fullTernary z x) =
      (kleinCyclicAction z (Multiplicative.ofAdd (augmentation x))).toAdd := by
  change augmentation ((fullC ^ z.toAdd.val) x) =
    ((localCycle.toAddEquiv.toMultiplicative ^ z.toAdd.val)
      (Multiplicative.ofAdd (augmentation x))).toAdd
  generalize z.toAdd.val = n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change augmentation (fullC ((fullC ^ n) x)) =
        localCycle (((localCycle.toAddEquiv.toMultiplicative ^ n)
          (Multiplicative.ofAdd (augmentation x))).toAdd)
      rw [fullC_augmentation, ih]

theorem fullTernary_fifth (z : Ternary) (x : FullCoordinates) :
    fullTernary z x 5 = x 5 := by
  change (fullC ^ z.toAdd.val) x 5 = x 5
  generalize z.toAdd.val = n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      exact ih

theorem fullLinear_augmentation (r : Complement) (x : FullCoordinates) :
    augmentation (fullComplementLinear r x) =
      (kleinCyclicAction r.right (Multiplicative.ofAdd (augmentation x))).toAdd := by
  change augmentation (fullKlein r.left (fullTernary r.right x)) = _
  rw [fullKlein_augmentation, fullTernary_augmentation]

theorem fullLinear_fifth (r : Complement) (x : FullCoordinates) :
    fullComplementLinear r x 5 = x 5 +
      r.left.toAdd 0 *
        (kleinCyclicAction r.right (Multiplicative.ofAdd (augmentation x))).toAdd 1 +
      r.left.toAdd 1 *
        (kleinCyclicAction r.right (Multiplicative.ofAdd (augmentation x))).toAdd 0 := by
  change fullTernary r.right x 5 +
    r.left.toAdd 0 * fullTernary r.right x 7 +
    r.left.toAdd 1 * fullTernary r.right x 6 = _
  have h0 := congrFun (fullTernary_augmentation r.right x) 0
  have h1 := congrFun (fullTernary_augmentation r.right x) 1
  change fullTernary r.right x 6 = _ at h0
  change fullTernary r.right x 7 = _ at h1
  rw [fullTernary_fifth, h0, h1]

def quadratic (p : Local) : Scalar := p 0 + p 1 + p 0 * p 1

theorem quadratic_polarize (p q : Local) :
    quadratic (p + q) = quadratic p + quadratic q + p 0 * q 1 + p 1 * q 0 := by
  simp only [quadratic, Pi.add_apply]
  ring

theorem quadratic_rotate (z : Ternary) (p : Local) :
    quadratic ((kleinCyclicAction z (Multiplicative.ofAdd p)).toAdd) = quadratic p := by
  revert z p
  decide +kernel

def tailSum (x : FullCoordinates) : Scalar := x 5 + x 2 + x 3 + x 4

theorem tailSum_add (x y : FullCoordinates) : tailSum (x + y) = tailSum x + tailSum y := by
  simp only [tailSum, Pi.add_apply]
  ring

theorem tailSum_fullKlein (p : Klein) (x : FullCoordinates) :
    tailSum (fullKlein p x) = tailSum x +
      p.toAdd 0 * (x 6 + x 7) + p.toAdd 1 * x 7 := by
  simp [tailSum, fullKlein, fullKleinFun]
  ring_nf
  simp only [show (2 : Scalar) = 0 from by decide +kernel,
    show (3 : Scalar) = 1 from by decide +kernel,
    mul_zero, mul_one, zero_add, add_zero]

theorem tailSum_fullC (x : FullCoordinates) : tailSum (fullC x) = tailSum x := by
  simp [tailSum, fullC]
  ring_nf
  simp only [show (3 : Scalar) = 1 from by decide +kernel, mul_one]

theorem tailSum_fullTernary (z : Ternary) (x : FullCoordinates) :
    tailSum (fullTernary z x) = tailSum x := by
  change tailSum ((fullC ^ z.toAdd.val) x) = tailSum x
  generalize z.toAdd.val = n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      change tailSum (fullC ((fullC ^ n) x)) = tailSum x
      rw [tailSum_fullC, ih]

theorem tailSum_fullLinear (r : Complement) (x : FullCoordinates) :
    tailSum (fullComplementLinear r x) = tailSum x +
      r.left.toAdd 0 *
        ((kleinCyclicAction r.right (Multiplicative.ofAdd (augmentation x))).toAdd 0 +
         (kleinCyclicAction r.right (Multiplicative.ofAdd (augmentation x))).toAdd 1) +
      r.left.toAdd 1 *
        (kleinCyclicAction r.right (Multiplicative.ofAdd (augmentation x))).toAdd 1 := by
  change tailSum (fullKlein r.left (fullTernary r.right x)) = _
  rw [tailSum_fullKlein, tailSum_fullTernary]
  have h0 := congrFun (fullTernary_augmentation r.right x) 0
  have h1 := congrFun (fullTernary_augmentation r.right x) 1
  change fullTernary r.right x 6 = _ at h0
  change fullTernary r.right x 7 = _ at h1
  rw [h0, h1]

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end
