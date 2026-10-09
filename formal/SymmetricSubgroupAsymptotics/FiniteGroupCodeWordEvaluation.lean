import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordCertificate

/-!
# Evaluate finite certificate words through an injective group code

Large reflected row groups should not have to replay their recursive row
multiplication merely to check a finite word.  This module evaluates the same
word in any executable injective code whose multiplication and inverse agree
with the group operations, then transports the resulting equality back to the
group.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- An executable faithful code for a group. -/
structure FiniteGroupCode (G Code : Type*) [Group G] where
  encode : G → Code
  injective : Function.Injective encode
  one : Code
  mul : Code → Code → Code
  inv : Code → Code
  encode_one : encode 1 = one
  encode_mul : ∀ x y, encode (x * y) = mul (encode x) (encode y)
  encode_inv : ∀ x, encode x⁻¹ = inv (encode x)

namespace FiniteGroupCode

variable {G H Code : Type*} [Group G] [Group H]

/-- Pull a faithful executable code back through an injective homomorphism. -/
def pullback (D : FiniteGroupCode H Code) (f : G →* H)
    (hf : Function.Injective f) : FiniteGroupCode G Code where
  encode := fun x ↦ D.encode (f x)
  injective := fun _ _ h ↦ hf (D.injective h)
  one := D.one
  mul := D.mul
  inv := D.inv
  encode_one := by rw [map_one, D.encode_one]
  encode_mul := by intro x y; rw [map_mul, D.encode_mul]
  encode_inv := by intro x; rw [map_inv, D.encode_inv]

end FiniteGroupCode

namespace FiniteGeneratorWord

variable {G Code ι : Type*} [Group G]

/-- Evaluate a generator word from the three executable code operations alone.
This separates reflected finite checks from a possibly noncomputable faithful
encoder used only by the soundness proof. -/
def evalCodeOps (one : Code) (mul : Code → Code → Code) (inv : Code → Code)
    (generators : ι → Code) : FiniteGeneratorWord ι → Code
  | .one => one
  | .generator i => generators i
  | .mul u v => mul (u.evalCodeOps one mul inv generators)
      (v.evalCodeOps one mul inv generators)
  | .inv u => inv (u.evalCodeOps one mul inv generators)

/-- Executable evaluation of a generator word in a faithful group code. -/
def evalCode (D : FiniteGroupCode G Code) (generators : ι → Code) :
    FiniteGeneratorWord ι → Code
  | .one => D.one
  | .generator i => generators i
  | .mul u v => D.mul (u.evalCode D generators) (v.evalCode D generators)
  | .inv u => D.inv (u.evalCode D generators)

theorem evalCodeOps_eq_evalCode (D : FiniteGroupCode G Code)
    (generators : ι → Code) (w : FiniteGeneratorWord ι) :
    w.evalCodeOps D.one D.mul D.inv generators = w.evalCode D generators := by
  induction w with
  | one => rfl
  | generator i => rfl
  | mul u v hu hv => exact congrArg₂ D.mul hu hv
  | inv u hu => exact congrArg D.inv hu

theorem encode_eval (D : FiniteGroupCode G Code)
    (generators : ι → G) (w : FiniteGeneratorWord ι) :
    D.encode (w.eval generators) =
      w.evalCode D (fun i ↦ D.encode (generators i)) := by
  induction w with
  | one => exact D.encode_one
  | generator i => rfl
  | mul u v hu hv => simpa only [eval, evalCode, D.encode_mul, hu, hv]
  | inv u hu => simpa only [eval, evalCode, D.encode_inv, hu]

/-- A code equality proves the corresponding literal word equation. -/
theorem eq_of_evalCode_eq (D : FiniteGroupCode G Code)
    (generators : ι → G) (w : FiniteGeneratorWord ι) (x : G)
    (h : w.evalCode D (fun i ↦ D.encode (generators i)) = D.encode x) :
    w.eval generators = x :=
  D.injective ((w.encode_eval D generators).trans h)

end FiniteGeneratorWord

namespace FiniteNormalJoinWord

variable {G Code κ : Type*} [Group G]

/-- Evaluate a normal-join word from executable code operations and an
explicit code for its literal conjugators. -/
def evalCodeOpsWith (one : Code) (mul : Code → Code → Code)
    (inv : Code → Code) (encodeConjugator : G → Code)
    (parent : κ → Code) (representative : Code) :
    FiniteNormalJoinWord κ G → Code
  | .one => one
  | .parent i => parent i
  | .conjugate g =>
      mul (mul (encodeConjugator g) representative) (inv (encodeConjugator g))
  | .mul u v => mul
      (u.evalCodeOpsWith one mul inv encodeConjugator parent representative)
      (v.evalCodeOpsWith one mul inv encodeConjugator parent representative)
  | .inv u => inv
      (u.evalCodeOpsWith one mul inv encodeConjugator parent representative)

/-- Executable evaluation of a normal-join word in a faithful group code. -/
def evalCode (D : FiniteGroupCode G Code) (parent : κ → Code)
    (representative : Code) : FiniteNormalJoinWord κ G → Code
  | .one => D.one
  | .parent i => parent i
  | .conjugate g => D.mul (D.mul (D.encode g) representative) (D.inv (D.encode g))
  | .mul u v => D.mul (u.evalCode D parent representative)
      (v.evalCode D parent representative)
  | .inv u => D.inv (u.evalCode D parent representative)

/-- Executable evaluation with an explicit code for conjugating elements.
This lets finite certificates use a small cache without changing the literal
group elements retained by the word. -/
def evalCodeWith (D : FiniteGroupCode G Code) (encodeConjugator : G → Code)
    (parent : κ → Code) (representative : Code) :
    FiniteNormalJoinWord κ G → Code
  | .one => D.one
  | .parent i => parent i
  | .conjugate g =>
      D.mul (D.mul (encodeConjugator g) representative)
        (D.inv (encodeConjugator g))
  | .mul u v =>
      D.mul (u.evalCodeWith D encodeConjugator parent representative)
        (v.evalCodeWith D encodeConjugator parent representative)
  | .inv u => D.inv (u.evalCodeWith D encodeConjugator parent representative)

theorem evalCodeOpsWith_eq_evalCodeWith (D : FiniteGroupCode G Code)
    (encodeConjugator : G → Code) (parent : κ → Code)
    (representative : Code) (w : FiniteNormalJoinWord κ G) :
    w.evalCodeOpsWith D.one D.mul D.inv encodeConjugator parent representative =
      w.evalCodeWith D encodeConjugator parent representative := by
  induction w with
  | one => rfl
  | parent i => rfl
  | conjugate g => rfl
  | mul u v hu hv => exact congrArg₂ D.mul hu hv
  | inv u hu => exact congrArg D.inv hu

/-- Exactly the conjugators on which an alternate executable encoder must
agree with the faithful group code. -/
def ConjugatorsSatisfy (P : G → Prop) : FiniteNormalJoinWord κ G → Prop
  | .one => True
  | .parent _ => True
  | .conjugate g => P g
  | .mul u v => u.ConjugatorsSatisfy P ∧ v.ConjugatorsSatisfy P
  | .inv u => u.ConjugatorsSatisfy P

theorem evalCodeWith_eq (D : FiniteGroupCode G Code)
    (encodeConjugator : G → Code) (parent : κ → Code)
    (representative : Code) (w : FiniteNormalJoinWord κ G)
    (h : w.ConjugatorsSatisfy (fun g ↦ encodeConjugator g = D.encode g)) :
    w.evalCodeWith D encodeConjugator parent representative =
      w.evalCode D parent representative := by
  induction w with
  | one => rfl
  | parent i => rfl
  | conjugate g =>
      change encodeConjugator g = D.encode g at h
      simp only [evalCodeWith, evalCode, h]
  | mul u v hu hv =>
      exact congrArg₂ D.mul (hu h.1) (hv h.2)
  | inv u hu => exact congrArg D.inv (hu h)

theorem encode_eval (D : FiniteGroupCode G Code) (parent : κ → G)
    (representative : G) (w : FiniteNormalJoinWord κ G) :
    D.encode (w.eval (parent := parent) representative) =
      w.evalCode D (fun i ↦ D.encode (parent i)) (D.encode representative) := by
  induction w with
  | one => exact D.encode_one
  | parent i => rfl
  | conjugate g =>
      simp only [eval, evalCode, D.encode_mul, D.encode_inv]
  | mul u v hu hv => simpa only [eval, evalCode, D.encode_mul, hu, hv]
  | inv u hu => simpa only [eval, evalCode, D.encode_inv, hu]

/-- A code equality proves the corresponding literal normal-join equation. -/
theorem eq_of_evalCode_eq (D : FiniteGroupCode G Code) (parent : κ → G)
    (representative : G) (w : FiniteNormalJoinWord κ G) (x : G)
    (h : w.evalCode D (fun i ↦ D.encode (parent i))
        (D.encode representative) = D.encode x) :
    w.eval (parent := parent) representative = x :=
  D.injective ((w.encode_eval D parent representative).trans h)

end FiniteNormalJoinWord

end SymmetricSubgroupAsymptotics

end
