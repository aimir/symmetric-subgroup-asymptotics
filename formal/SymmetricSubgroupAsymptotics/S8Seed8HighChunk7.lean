import SymmetricSubgroupAsymptotics.S8Seed8NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteNormalizerExtensionWordFamily
import Mathlib.Data.Fin.VecNotation

/-! One selected bounded family of actual larger binary extensions.
All ordinary words, power equations, seed nonmembership and permutation
coordinates are checked by Lean's kernel. No root-order flag is input. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed8HighChunk7
open S8Seed8LeftCosets

def indices : Fin 9 → Fin 102 := ![92, 93, 94, 95, 96, 98, 99, 100, 101]

def images (i : Fin 9) : Fin 8 → Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 5, 2, 7, 4, 1, 6, 3] else ![0, 5, 2, 7, 4, 1, 6, 3]) else (if i.val < 3 then ![0, 5, 2, 7, 4, 1, 6, 3] else ![0, 5, 2, 7, 4, 1, 6, 3])) else (if i.val < 6 then (if i.val < 5 then ![0, 5, 2, 7, 4, 1, 6, 3] else ![0, 5, 2, 7, 4, 1, 6, 3]) else (if i.val < 7 then ![0, 5, 2, 7, 4, 1, 6, 3] else (if i.val < 8 then ![0, 5, 2, 7, 4, 1, 6, 3] else ![0, 5, 2, 7, 4, 1, 6, 3]))))

def inverseImages (i : Fin 9) : Fin 8 → Fin 8 :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![0, 5, 2, 7, 4, 1, 6, 3] else ![0, 5, 2, 7, 4, 1, 6, 3]) else (if i.val < 3 then ![0, 5, 2, 7, 4, 1, 6, 3] else ![0, 5, 2, 7, 4, 1, 6, 3])) else (if i.val < 6 then (if i.val < 5 then ![0, 5, 2, 7, 4, 1, 6, 3] else ![0, 5, 2, 7, 4, 1, 6, 3]) else (if i.val < 7 then ![0, 5, 2, 7, 4, 1, 6, 3] else (if i.val < 8 then ![0, 5, 2, 7, 4, 1, 6, 3] else ![0, 5, 2, 7, 4, 1, 6, 3]))))

set_option maxHeartbeats 1000000 in
private theorem left_checked : ∀ (i : Fin 9) (x : Fin 8),
    inverseImages i (images i x) = x := by decide +kernel
set_option maxHeartbeats 1000000 in
private theorem right_checked : ∀ (i : Fin 9) (x : Fin 8),
    images i (inverseImages i x) = x := by decide +kernel

def elements (i : Fin 9) : Ambient where
  toFun := images i
  invFun := inverseImages i
  left_inv := left_checked i
  right_inv := right_checked i

def sourceGenerators (i : Fin 9) : Fin 3 → Ambient :=
  Matrix.vecCons (representatives (S8Seed8NormalizerRoots.roots (indices i)))
    BinaryMenuCayley8T8.generators

def forwardWords (i : Fin 9) : Fin 2 → FiniteGeneratorWord (Fin 2) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)] else ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)]) else (if i.val < 3 then ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)] else ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)])) else (if i.val < 6 then (if i.val < 5 then ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)] else ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)]) else (if i.val < 7 then ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)] else (if i.val < 8 then ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)] else ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)]))))

def backwardWords (i : Fin 9) : Fin 2 → FiniteGeneratorWord (Fin 2) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)] else ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)]) else (if i.val < 3 then ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)] else ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)])) else (if i.val < 6 then (if i.val < 5 then ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)] else ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)]) else (if i.val < 7 then ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)] else (if i.val < 8 then ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)] else ![(.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))), (.generator 1)]))))

def inclusionWords (i : Fin 9) : FiniteGeneratorWord (Fin 3) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (.mul (.mul (.mul (.generator 1) (.mul (.generator 2) (.inv (.generator 1)))) (.mul (.generator 0) (.mul (.generator 1) (.generator 0)))) (.mul (.mul (.inv (.generator 1)) (.mul (.generator 0) (.generator 1))) (.mul (.generator 0) (.mul (.inv (.generator 1)) (.generator 0))))) else (.mul (.mul (.mul (.generator 1) (.mul (.generator 2) (.inv (.generator 1)))) (.mul (.mul (.inv (.generator 1)) (.inv (.generator 1))) (.mul (.inv (.generator 1)) (.inv (.generator 0))))) (.mul (.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))) (.mul (.mul (.inv (.generator 0)) (.inv (.generator 1))) (.mul (.generator 0) (.generator 0)))))) else (if i.val < 3 then (.mul (.mul (.mul (.generator 1) (.mul (.generator 2) (.inv (.generator 2)))) (.mul (.generator 1) (.mul (.inv (.generator 2)) (.generator 0)))) (.mul (.mul (.generator 1) (.mul (.inv (.generator 0)) (.inv (.generator 1)))) (.mul (.generator 0) (.mul (.generator 1) (.inv (.generator 0)))))) else (.mul (.mul (.mul (.generator 1) (.mul (.generator 2) (.inv (.generator 1)))) (.mul (.mul (.inv (.generator 1)) (.inv (.generator 1))) (.mul (.inv (.generator 1)) (.generator 0)))) (.mul (.mul (.generator 0) (.mul (.generator 1) (.generator 0))) (.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 0) (.generator 0))))))) else (if i.val < 6 then (if i.val < 5 then (.mul (.mul (.generator 1) (.mul (.generator 2) (.inv (.generator 1)))) (.mul (.generator 0) (.mul (.generator 2) (.inv (.generator 0))))) else (.mul (.mul (.mul (.generator 1) (.generator 2)) (.mul (.generator 1) (.inv (.generator 0)))) (.mul (.mul (.generator 1) (.generator 2)) (.mul (.inv (.generator 1)) (.generator 0))))) else (if i.val < 7 then (.mul (.mul (.mul (.generator 1) (.generator 2)) (.mul (.generator 1) (.mul (.inv (.generator 2)) (.inv (.generator 1))))) (.mul (.mul (.generator 0) (.generator 0)) (.mul (.generator 1) (.mul (.generator 0) (.generator 0))))) else (if i.val < 8 then (.mul (.mul (.generator 1) (.mul (.generator 2) (.inv (.generator 1)))) (.mul (.generator 0) (.mul (.generator 2) (.inv (.generator 0))))) else (.mul (.mul (.generator 1) (.mul (.generator 2) (.inv (.generator 2)))) (.mul (.generator 0) (.mul (.generator 1) (.generator 0))))))))

set_option maxHeartbeats 1000000 in
private theorem forward_checked : ∀ (i : Fin 9) (j : Fin 2),
    (forwardWords i j).eval BinaryMenuCayley8T8.generators =
      (MulAut.conj (elements i)) (BinaryMenuCayley8T8.generators j) := by
  intro i j
  apply Equiv.ext
  intro x
  revert i j x
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem backward_checked : ∀ (i : Fin 9) (j : Fin 2),
    (backwardWords i j).eval BinaryMenuCayley8T8.generators =
      (MulAut.conj (elements i)).symm (BinaryMenuCayley8T8.generators j) := by
  intro i j
  apply Equiv.ext
  intro x
  revert i j x
  decide +kernel

def normalizerCertificate (i : Fin 9) :
    FiniteGeneratorEquivWordCertificate (MulAut.conj (elements i))
      BinaryMenuCayley8T8.generators BinaryMenuCayley8T8.generators where
  forward := { words := forwardWords i, equations := forward_checked i }
  backward := { words := backwardWords i, equations := backward_checked i }

set_option maxHeartbeats 1000000 in
private theorem powers_checked : ∀ i : Fin 9, elements i ^ (2 ^ 3) = 1 := by
  intro i
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem outside_checked : ∀ i : Fin 9, elements i ∉ H := by
  intro i
  change elements i ∉ Subgroup.closure (Set.range BinaryMenuCayley8T8.generators)
  rw [BinaryMenuCayley8T8.certificate.mem_closure_iff]
  revert i
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem inclusion_checked : ∀ i : Fin 9,
    (inclusionWords i).eval (sourceGenerators i) = elements i := by
  intro i
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def family : FiniteNormalizerExtensionWordFamily
    BinaryMenuCayley8T8.generators sourceGenerators 2 3 where
  elements := elements
  normalizer := normalizerCertificate
  power_eq_one := powers_checked
  outside_seed := outside_checked
  inclusionWords := inclusionWords
  inclusion_eq := inclusion_checked

theorem source_closure (i : Fin 9) :
    Subgroup.closure (Set.range (sourceGenerators i)) =
      H ⊔ Subgroup.closure {representatives (S8Seed8NormalizerRoots.roots (indices i))} := by
  simp only [sourceGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

abbrev extendedSeed (i : Fin 9) : Subgroup Ambient := family.extension i

theorem extended_isPGroup (i : Fin 9) : IsPGroup 2 (extendedSeed i) :=
  family.extension_isPGroup (IsPGroup.of_card (n := 4) BinaryMenuCayley8T8.exact_card) i

theorem extended_card_gt (i : Fin 9) : 16 < Nat.card (extendedSeed i) := by
  have h := family.card_lt_extension i
  rw [BinaryMenuCayley8T8.exact_card] at h
  exact h

theorem extended_le_adjoin (i : Fin 9) : extendedSeed i ≤
    H ⊔ Subgroup.closure {representatives (S8Seed8NormalizerRoots.roots (indices i))} := by
  have h := family.extension_le_source i (by rw [source_closure]; exact le_sup_left)
  rw [source_closure] at h
  exact h

end SymmetricSubgroupAsymptotics.S8Seed8HighChunk7
end
