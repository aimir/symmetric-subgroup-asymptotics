import SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation
import SymmetricSubgroupAsymptotics.SemidirectAbelianCentralizer

/-! A common symbolic complement and its two augmentation modules.
The complement is the displayed `2^2 ⋊ 3`, and the Boolean parameter
selects the five-dimensional submodule or the full six-dimensional one.
No order or normal-subgroup census is used. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourBlockAugmentation

open SemidirectProduct

abbrev Ternary := Multiplicative (ZMod 3)
abbrev Klein := Multiplicative Local

/-- Powers of an element whose order divides the displayed modulus. -/
def powersHom {H : Type} [Group H] (n : ℕ) [NeZero n]
    (g : H) (hg : g ^ n = 1) : Multiplicative (ZMod n) →* H where
  toFun z := g ^ z.toAdd.val
  map_one' := by simp
  map_mul' z w := by
    change g ^ (z.toAdd + w.toAdd).val = g ^ z.toAdd.val * g ^ w.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    symm
    calc
      g ^ (z.toAdd.val + w.toAdd.val) =
          g ^ ((z.toAdd.val + w.toAdd.val) % n +
            n * ((z.toAdd.val + w.toAdd.val) / n)) :=
        congrArg (g ^ ·) (Nat.mod_add_div _ n).symm
      _ = g ^ ((z.toAdd.val + w.toAdd.val) % n) := by
        rw [pow_add, pow_mul, hg, one_pow, mul_one]

theorem localCycle_cube : localCycle ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

def kleinCyclicAction : Ternary →* MulAut Klein :=
  powersHom 3 localCycle.toAddEquiv.toMultiplicative (by
    apply MulEquiv.ext
    intro x
    change localCycle (localCycle (localCycle x.toAdd)) = x.toAdd
    exact congrArg (fun f : Local ≃ₗ[Scalar] Local => f x.toAdd) localCycle_cube)

abbrev Complement := Klein ⋊[kleinCyclicAction] Ternary

instance : Finite Complement :=
  Finite.of_equiv (Klein × Ternary) SemidirectProduct.equivProd.symm

/-- The Klein action is unipotent of length two: only the diagonal
coordinates change. -/
def kleinLinear (p : Klein) : Coordinates ≃ₗ[Scalar] Coordinates where
  toFun x :=
    ![x 0 + p.toAdd 0 * (x 4 + x 5) + p.toAdd 1 * (x 3 + x 4),
      x 1 + p.toAdd 0 * (x 2 + x 4 + x 5) + p.toAdd 1 * x 4,
      x 2, x 3, x 4, x 5]
  invFun x :=
    ![x 0 + p.toAdd 0 * (x 4 + x 5) + p.toAdd 1 * (x 3 + x 4),
      x 1 + p.toAdd 0 * (x 2 + x 4 + x 5) + p.toAdd 1 * x 4,
      x 2, x 3, x 4, x 5]
  left_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel, mul_zero, add_zero]
  right_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel, mul_zero, add_zero]
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro a x
    ext i
    fin_cases i <;> simp <;> ring

def kleinLinearHom : Klein →* (Coordinates ≃ₗ[Scalar] Coordinates) where
  toFun := kleinLinear
  map_one' := by
    apply LinearEquiv.ext
    intro x
    ext i
    fin_cases i <;> simp [kleinLinear]
  map_mul' p q := by
    apply LinearEquiv.ext
    intro x
    ext i
    fin_cases i <;> simp [kleinLinear] <;> ring

theorem c_cube : c ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

def ternaryLinear : Ternary →* (Coordinates ≃ₗ[Scalar] Coordinates) :=
  powersHom 3 c c_cube

theorem complementCompatibility (z : Ternary) :
    kleinLinearHom.comp (kleinCyclicAction z).toMonoidHom =
      (MulAut.conj (ternaryLinear z)).toMonoidHom.comp kleinLinearHom := by
  apply MonoidHom.ext
  intro p
  apply LinearEquiv.ext
  intro x
  change kleinLinear (kleinCyclicAction z p) x =
    (ternaryLinear z * kleinLinear p * (ternaryLinear z)⁻¹) x
  revert z p x
  decide +kernel

def complementLinear : Complement →* (Coordinates ≃ₗ[Scalar] Coordinates) :=
  SemidirectProduct.lift kleinLinearHom ternaryLinear complementCompatibility

theorem complementLinear_last (r : Complement) (x : Coordinates) :
    complementLinear r x 5 = x 5 := by
  change kleinLinear r.left (c ^ r.right.toAdd.val <| x) 5 = x 5
  change (c ^ r.right.toAdd.val) x 5 = x 5
  generalize r.right.toAdd.val = n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      exact ih

/-- The row9 translation module is the codimension-one submodule;
row11 uses the whole augmentation module. -/
def space (full : Bool) : Submodule Scalar Coordinates where
  carrier := {x | full = false → x 5 = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy h; simp [hx h, hy h]
  smul_mem' := by intro a x hx h; simp [hx h]

def restrictedLinear (full : Bool) (r : Complement) :
    space full ≃ₗ[Scalar] space full where
  toFun x := ⟨complementLinear r x, fun h => by
    rw [complementLinear_last]; exact x.property h⟩
  invFun x := ⟨complementLinear r⁻¹ x, fun h => by
    rw [complementLinear_last]; exact x.property h⟩
  left_inv x := by
    apply Subtype.ext
    change (complementLinear r⁻¹ * complementLinear r) (x : Coordinates) = x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv x := by
    apply Subtype.ext
    change (complementLinear r * complementLinear r⁻¹) (x : Coordinates) = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  map_add' x y := Subtype.ext ((complementLinear r).map_add x y)
  map_smul' a x := Subtype.ext ((complementLinear r).map_smul a x)

def restrictedLinearHom (full : Bool) :
    Complement →* (space full ≃ₗ[Scalar] space full) where
  toFun := restrictedLinear full
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : Coordinates ≃ₗ[Scalar] Coordinates => f x)
      complementLinear.map_one
  map_mul' r s := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : Coordinates ≃ₗ[Scalar] Coordinates => f x)
      (complementLinear.map_mul r s)

def action (full : Bool) : Complement →* MulAut (Multiplicative (space full)) where
  toFun r := (restrictedLinear full r).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro x
    exact congrArg (fun f : space full ≃ₗ[Scalar] space full =>
      Multiplicative.ofAdd (f x.toAdd)) (restrictedLinearHom full).map_one
  map_mul' r s := by
    apply MulEquiv.ext
    intro x
    exact congrArg (fun f : space full ≃ₗ[Scalar] space full =>
      Multiplicative.ofAdd (f x.toAdd)) ((restrictedLinearHom full).map_mul r s)

abbrev Model (full : Bool) := Multiplicative (space full) ⋊[action full] Complement

instance (full : Bool) : Finite (Model full) :=
  Finite.of_equiv (Multiplicative (space full) × Complement)
    SemidirectProduct.equivProd.symm

def basis (full : Bool) (i : Fin 5) : space full :=
  ⟨basisVector i.castSucc, by intro h; fin_cases i <;> decide +kernel⟩

/-- Three displayed vectors detect the complement action, in both
translation modules. This is a fixed binary coordinate identity. -/
theorem complement_detect (p : Klein) (z : Ternary)
    (h0 : complementLinear ⟨p, z⟩ (basisVector 0) = basisVector 0)
    (h2 : complementLinear ⟨p, z⟩ (basisVector 2) = basisVector 2)
    (h3 : complementLinear ⟨p, z⟩ (basisVector 3) = basisVector 3) :
    p = 1 ∧ z = 1 := by
  have detect : ∀ (a b : Scalar) (s : ZMod 3),
      complementLinear ⟨Multiplicative.ofAdd ![a, b], Multiplicative.ofAdd s⟩
          (basisVector 0) 1 = 0 →
      complementLinear ⟨Multiplicative.ofAdd ![a, b], Multiplicative.ofAdd s⟩
          (basisVector 2) 1 = 0 →
      complementLinear ⟨Multiplicative.ofAdd ![a, b], Multiplicative.ofAdd s⟩
          (basisVector 3) 0 = 0 →
      a = 0 ∧ b = 0 ∧ s = 0 := by decide +kernel
  have hp : Multiplicative.ofAdd ![p.toAdd 0, p.toAdd 1] = p := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> rfl
  have hd := detect (p.toAdd 0) (p.toAdd 1) z.toAdd
  rw [hp] at hd
  obtain ⟨hp0, hp1, hz⟩ := hd
    (congrArg (fun x : Coordinates => x 1) h0)
    (congrArg (fun x : Coordinates => x 1) h2)
    (congrArg (fun x : Coordinates => x 0) h3)
  refine ⟨?_, Multiplicative.toAdd.injective hz⟩
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i
  · exact hp0
  · exact hp1

theorem action_injective (full : Bool) : Function.Injective (action full) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have h (i : Fin 5) : complementLinear r (basisVector i.castSucc) =
      basisVector i.castSucc := by
    exact congrArg (fun f : MulAut (Multiplicative (space full)) =>
      ((f (Multiplicative.ofAdd (basis full i))).toAdd : Coordinates)) hr
  obtain ⟨hp, hz⟩ := complement_detect r.left r.right (h 0) (h 2) (h 3)
  exact SemidirectProduct.ext hp hz

def uElement : Complement := inl (Multiplicative.ofAdd ![1, 0])
def vElement : Complement := inl (Multiplicative.ofAdd ![0, 1])
def cElement : Complement := inr (Multiplicative.ofAdd 1)

theorem linear_u (x : Coordinates) : complementLinear uElement x = u x := by
  revert x; decide +kernel
theorem linear_v (x : Coordinates) : complementLinear vElement x = v x := by
  revert x; decide +kernel
theorem linear_c (x : Coordinates) : complementLinear cElement x = c x := by
  revert x; decide +kernel

end BinaryFourBlockAugmentation
end SymmetricSubgroupAsymptotics

end
