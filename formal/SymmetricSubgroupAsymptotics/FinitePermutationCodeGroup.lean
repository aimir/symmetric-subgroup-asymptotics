import SymmetricSubgroupAsymptotics.FiniteGroupCodeWordEvaluation
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding

/-! Executable group operations on faithful finite-permutation codes. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Composition of two base-`n` function codes. -/
def permutationCodeMul {n : ℕ} (x y : Fin (n ^ n)) : Fin (n ^ n) :=
  finFunctionFinEquiv (fun i ↦
    finFunctionFinEquiv.symm x (finFunctionFinEquiv.symm y i))

@[simp] theorem permutationCode_mul {n : ℕ}
    (x y : Equiv.Perm (Fin n)) :
    permutationCode (x * y) =
      permutationCodeMul (permutationCode x) (permutationCode y) := by
  unfold permutationCode permutationCodeMul
  apply congrArg finFunctionFinEquiv
  funext i
  simp

/-- Forward and inverse codes. Carrying both makes inversion a constant-time
swap while retaining a finite type with cheap decidable equality. -/
abbrev PermutationCodePair (n : ℕ) := Fin (n ^ n) × Fin (n ^ n)

def permutationCodePair {n : ℕ} (x : Equiv.Perm (Fin n)) :
    PermutationCodePair n :=
  (permutationCode x, permutationCode x⁻¹)

def permutationCodePairOne (n : ℕ) : PermutationCodePair n :=
  permutationCodePair 1

def permutationCodePairMul {n : ℕ}
    (x y : PermutationCodePair n) : PermutationCodePair n :=
  (permutationCodeMul x.1 y.1, permutationCodeMul y.2 x.2)

def permutationCodePairInv {n : ℕ}
    (x : PermutationCodePair n) : PermutationCodePair n :=
  (x.2, x.1)

@[simp] theorem permutationCodePair_one {n : ℕ} :
    permutationCodePair (1 : Equiv.Perm (Fin n)) = permutationCodePairOne n :=
  rfl

@[simp] theorem permutationCodePair_mul {n : ℕ}
    (x y : Equiv.Perm (Fin n)) :
    permutationCodePair (x * y) =
      permutationCodePairMul (permutationCodePair x) (permutationCodePair y) := by
  ext <;> simp [permutationCodePair, permutationCodePairMul]

@[simp] theorem permutationCodePair_inv {n : ℕ}
    (x : Equiv.Perm (Fin n)) :
    permutationCodePair x⁻¹ = permutationCodePairInv (permutationCodePair x) := by
  ext <;> simp [permutationCodePair, permutationCodePairInv]

/-- Forward and inverse functions.  This is the fastest executable code for
small permutation degrees: multiplication is pointwise composition and
inversion swaps the two functions. -/
abbrev PermutationFunctionPair (n : ℕ) :=
  (Fin n → Fin n) × (Fin n → Fin n)

def permutationFunctionPair {n : ℕ} (x : Equiv.Perm (Fin n)) :
    PermutationFunctionPair n :=
  (fun i ↦ x i, fun i ↦ (x⁻¹) i)

def permutationFunctionPairOne (n : ℕ) : PermutationFunctionPair n :=
  (id, id)

def permutationFunctionPairMul {n : ℕ}
    (x y : PermutationFunctionPair n) : PermutationFunctionPair n :=
  (fun i ↦ x.1 (y.1 i), fun i ↦ y.2 (x.2 i))

def permutationFunctionPairInv {n : ℕ}
    (x : PermutationFunctionPair n) : PermutationFunctionPair n :=
  (x.2, x.1)

@[simp] theorem permutationFunctionPair_one {n : ℕ} :
    permutationFunctionPair (1 : Equiv.Perm (Fin n)) =
      permutationFunctionPairOne n := by
  ext <;> rfl

@[simp] theorem permutationFunctionPair_mul {n : ℕ}
    (x y : Equiv.Perm (Fin n)) :
    permutationFunctionPair (x * y) =
      permutationFunctionPairMul (permutationFunctionPair x)
        (permutationFunctionPair y) := by
  ext <;> rfl

@[simp] theorem permutationFunctionPair_inv {n : ℕ}
    (x : Equiv.Perm (Fin n)) :
    permutationFunctionPair x⁻¹ =
      permutationFunctionPairInv (permutationFunctionPair x) := by
  ext <;> rfl

/-- Faithful executable function-pair code for a permutation group. -/
def permutationFunctionPairCode (n : ℕ) :
    FiniteGroupCode (Equiv.Perm (Fin n)) (PermutationFunctionPair n) where
  encode := permutationFunctionPair
  injective := by
    intro x y h
    exact Equiv.ext (congrFun (congrArg Prod.fst h))
  one := permutationFunctionPairOne n
  mul := permutationFunctionPairMul
  inv := permutationFunctionPairInv
  encode_one := permutationFunctionPair_one
  encode_mul := permutationFunctionPair_mul
  encode_inv := permutationFunctionPair_inv

end SymmetricSubgroupAsymptotics

end
