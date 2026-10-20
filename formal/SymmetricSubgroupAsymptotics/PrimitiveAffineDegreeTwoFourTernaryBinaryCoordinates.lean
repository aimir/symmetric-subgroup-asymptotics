import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryCoordinates
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import Mathlib.GroupTheory.PGroup

/-!
# Binary coordinates for the eight four-ternary complements

Four sign bits and two block bits give the common coordinate frame. Five
explicit predicates select the actual complements. Canonical words recover
every permitted coordinate from the displayed generators, including the
coupled sign/block condition in row 214. All finite certificates concern
these six binary coordinates; no original top or subgroup registry is used.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoFourTernaryBinaryCoordinates

open TernarySignedBlockCoordinates
open PrimitiveAffineDegreeTwoFourTernaryCoordinates

abbrev Bit := ZMod 2
abbrev Sign := Multiplicative Bit
abbrev Klein := Multiplicative (Bit × Bit)

def blockHom : Klein →* Equiv.Perm (Fin 4) where
  toFun h := blockOne ^ h.toAdd.1.val * blockTwo ^ h.toAdd.2.val
  map_one' := by apply Equiv.ext; intro i; revert i; decide +kernel
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro i
    revert g h i
    decide +kernel

theorem blockHom_injective : Function.Injective blockHom := by
  intro g h he
  have he0 := congrArg (fun p : Equiv.Perm (Fin 4) => p 0) he
  have hc : ∀ g h : Klein, blockHom g 0 = blockHom h 0 → g = h := by decide +kernel
  exact hc g h he0

instance : MulAction Klein (Fin 4) := MulAction.compHom (Fin 4) blockHom

def signHom : Sign →* Scalarˣ where
  toFun b := if b.toAdd = 0 then 1 else -1
  map_one' := rfl
  map_mul' := by decide +kernel

theorem signHom_injective : Function.Injective signHom := by decide +kernel

abbrev Frame := PermutationalWreathProduct Sign Klein (Fin 4)

def frameEquiv : Frame ≃ (Fin 4 → Sign) × Klein where
  toFun q := (q.left, q.right)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Frame := Fintype.ofEquiv _ frameEquiv.symm

instance : DecidableEq Frame := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    ⟨fun h => PermutationalWreathProduct.ext h.1 h.2,
      fun h => ⟨congrArg (fun q : Frame => q.left) h,
        congrArg (fun q : Frame => q.right) h⟩⟩

/-- The exact signed-permutation realization of the six binary coordinates. -/
def toSigned : Frame →* Signed where
  toFun q := ⟨fun i => signHom (q.left i), blockHom q.right⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i; exact map_one signHom
    · exact map_one blockHom
  map_mul' g h := by
    apply PermutationalWreathProduct.ext
    · funext i
      change signHom (g.left i * h.left (blockHom g.right⁻¹ i)) =
        signHom (g.left i) * signHom (h.left ((blockHom g.right)⁻¹ i))
      rw [map_mul, map_inv]
    · exact map_mul blockHom g.right h.right

theorem toSigned_injective : Function.Injective toSigned := by
  intro g h he
  apply PermutationalWreathProduct.ext
  · funext i
    apply signHom_injective
    exact congrArg (fun q : Signed => q.left i) he
  · apply blockHom_injective
    exact congrArg (fun q : Signed => q.right) he

def bit (q : Frame) (i : Fin 4) : Bit := (q.left i).toAdd
def low (q : Frame) : Bit := q.right.toAdd.1
def high (q : Frame) : Bit := q.right.toAdd.2

/-- Constant, paired, twisted, even, and unrestricted sign conditions. -/
def allowed (s : Fin 5) (q : Frame) : Prop :=
  match s.val with
  | 0 => bit q 0 = bit q 1 ∧ bit q 1 = bit q 2 ∧ bit q 2 = bit q 3
  | 1 => bit q 0 = bit q 2 ∧ bit q 1 = bit q 3
  | 2 => bit q 0 + bit q 2 = bit q 1 + bit q 3 ∧
      bit q 0 + bit q 2 = low q + high q
  | 3 => bit q 0 + bit q 1 + bit q 2 + bit q 3 = 0
  | _ => True

instance (s : Fin 5) (q : Frame) : Decidable (allowed s q) := by
  unfold allowed
  split <;> infer_instance

def shape : Fin 8 → Fin 5 := ![0, 1, 0, 0, 1, 2, 3, 4]

def binarySubgroup (s : Fin 5) : Subgroup Frame where
  carrier := allowed s
  one_mem' := by
    change allowed s 1
    fin_cases s <;> decide +kernel
  mul_mem' := by
    have h : ∀ a b : Frame, allowed s a → allowed s b → allowed s (a * b) := by
      fin_cases s <;> decide +kernel
    exact fun a b ha hb => h a b ha hb
  inv_mem' := by
    have h : ∀ a : Frame, allowed s a → allowed s a⁻¹ := by
      fin_cases s <;> decide +kernel
    exact fun a ha => h a ha

abbrev Complement (r : Fin 8) := binarySubgroup (shape r)

instance (r : Fin 8) : DecidablePred (fun q : Frame => q ∈ Complement r) :=
  fun q => inferInstanceAs (Decidable (allowed (shape r) q))

def frame (b : Fin 4 → Bit) (x y : Bit) : Frame :=
  ⟨fun i => Multiplicative.ofAdd (b i), Multiplicative.ofAdd (x, y)⟩

def frameGenerators : Fin 8 → Fin 5 → Frame :=
  let all := frame ![1, 1, 1, 1] 0 0
  let odd := frame ![0, 1, 0, 1] 0 0
  let hi := frame ![0, 0, 1, 1] 0 0
  let last := frame ![0, 0, 0, 1] 0 0
  let a := frame 0 1 0
  let b := frame 0 0 1
  let twisted := frame ![0, 1, 1, 0] 0 1
  let c := frame 0 1 1
  ![![1, all, a, b, 1], ![1, odd, a, b, 1],
    ![1, all, a, b, 1], ![1, all, a, b, 1],
    ![1, odd, a, b, 1], ![1, odd, twisted, c, 1],
    ![1, hi, odd, a, b], ![1, last, a, b, 1]]

theorem frameGenerators_mem (r : Fin 8) (j : Fin 5) :
    frameGenerators r j ∈ Complement r := by
  fin_cases r <;> fin_cases j <;> decide +kernel

theorem frameGenerators_binding (r : Fin 8) (j : Fin 5) :
    toSigned (frameGenerators r j) = (generators r j).right := by
  fin_cases r <;> fin_cases j <;> apply PermutationalWreathProduct.ext
  all_goals first
    | (funext i; apply Units.ext; revert i; decide +kernel)
    | (apply Equiv.ext; intro i; revert i; decide +kernel)

abbrev Word := FiniteGeneratorWord (Fin 5)

def letter (i : Fin 5) : Word := .generator i
def whenBit (b : Bit) (w : Word) : Word := if b = 0 then .one else w
def conjugateWord (u v : Word) : Word := .mul (.mul u v) (.inv u)

def constantWord (q : Frame) : Word :=
  .mul (.mul (whenBit (bit q 0) (letter 1))
    (whenBit (low q) (letter 2))) (whenBit (high q) (letter 3))

def pairedWord (q : Frame) : Word :=
  .mul (.mul (.mul
    (whenBit (bit q 0) (conjugateWord (letter 2) (letter 1)))
    (whenBit (bit q 1) (letter 1)))
    (whenBit (low q) (letter 2))) (whenBit (high q) (letter 3))

def twistedWord (q : Frame) : Word :=
  .mul (.mul (.mul
    (whenBit (bit q 0) (conjugateWord (letter 3) (letter 1)))
    (whenBit (bit q 1 + low q + high q) (letter 1)))
    (whenBit (low q + high q) (letter 2))) (whenBit (low q) (letter 3))

def evenWord (q : Frame) : Word :=
  .mul (.mul (.mul (.mul
    (whenBit (bit q 0) (conjugateWord (letter 4) (letter 1)))
    (whenBit (bit q 1 + bit q 0) (letter 2)))
    (whenBit (bit q 2) (letter 1)))
    (whenBit (low q) (letter 3))) (whenBit (high q) (letter 4))

def fullWord (q : Frame) : Word :=
  .mul (.mul (.mul (.mul (.mul
    (whenBit (bit q 0) (conjugateWord (.mul (letter 2) (letter 3)) (letter 1)))
    (whenBit (bit q 1) (conjugateWord (letter 3) (letter 1))))
    (whenBit (bit q 2) (conjugateWord (letter 2) (letter 1))))
    (whenBit (bit q 3) (letter 1)))
    (whenBit (low q) (letter 2))) (whenBit (high q) (letter 3))

def canonicalWord : Fin 8 → Frame → Word :=
  ![constantWord, pairedWord, constantWord, constantWord, pairedWord,
    twistedWord, evenWord, fullWord]

/-- A closed word formula, rather than a search or an element table. -/
theorem canonicalWord_eq (r : Fin 8) (q : Frame) (hq : q ∈ Complement r) :
    (canonicalWord r q).eval (frameGenerators r) = q := by
  fin_cases r <;> revert q hq <;> decide +kernel

theorem complement_eq_closure (r : Fin 8) :
    Complement r = Subgroup.closure (Set.range (frameGenerators r)) := by
  apply le_antisymm
  · intro q hq
    rw [← canonicalWord_eq r q hq]
    exact (canonicalWord r q).eval_mem_closure (frameGenerators r)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact frameGenerators_mem r j

def complementExponent : Fin 8 → ℕ := ![3, 4, 3, 3, 4, 4, 5, 6]

theorem complement_card (r : Fin 8) :
    Nat.card (Complement r) = 2 ^ complementExponent r := by
  rw [Nat.card_eq_fintype_card]
  fin_cases r <;> decide +kernel

theorem complement_binary (r : Fin 8) : IsPGroup 2 (Complement r) :=
  IsPGroup.of_card (complement_card r)

end PrimitiveAffineDegreeTwoFourTernaryBinaryCoordinates
end SymmetricSubgroupAsymptotics

end
