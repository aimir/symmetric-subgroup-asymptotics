import SymmetricSubgroupAsymptotics.S8Seed9NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteNormalizerExtensionWordFamily
import Mathlib.Data.Fin.VecNotation

/-! One selected bounded family of actual larger binary extensions.
All ordinary words, power equations, seed nonmembership and permutation
coordinates are checked by Lean's kernel. No root-order flag is input. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed9HighChunk11
open S8Seed9LeftCosets

def indices : Fin 13 → Fin 164 := ![146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]

def images (i : Fin 13) : Fin 8 → Fin 8 :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ![0, 2, 1, 4, 3, 5, 6, 7] else (if i.val < 2 then ![0, 2, 1, 4, 3, 5, 6, 7] else ![0, 2, 1, 4, 3, 5, 6, 7])) else (if i.val < 4 then ![2, 7, 0, 4, 3, 6, 5, 1] else (if i.val < 5 then ![0, 2, 1, 4, 3, 5, 6, 7] else ![0, 2, 1, 4, 3, 5, 6, 7]))) else (if i.val < 9 then (if i.val < 7 then ![0, 2, 1, 4, 3, 5, 6, 7] else (if i.val < 8 then ![2, 7, 0, 4, 3, 6, 5, 1] else ![0, 2, 1, 4, 3, 5, 6, 7])) else (if i.val < 11 then (if i.val < 10 then ![0, 2, 1, 4, 3, 5, 6, 7] else ![0, 2, 1, 4, 3, 5, 6, 7]) else (if i.val < 12 then ![0, 2, 1, 4, 3, 5, 6, 7] else ![0, 2, 1, 4, 3, 5, 6, 7]))))

def inverseImages (i : Fin 13) : Fin 8 → Fin 8 :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ![0, 2, 1, 4, 3, 5, 6, 7] else (if i.val < 2 then ![0, 2, 1, 4, 3, 5, 6, 7] else ![0, 2, 1, 4, 3, 5, 6, 7])) else (if i.val < 4 then ![2, 7, 0, 4, 3, 6, 5, 1] else (if i.val < 5 then ![0, 2, 1, 4, 3, 5, 6, 7] else ![0, 2, 1, 4, 3, 5, 6, 7]))) else (if i.val < 9 then (if i.val < 7 then ![0, 2, 1, 4, 3, 5, 6, 7] else (if i.val < 8 then ![2, 7, 0, 4, 3, 6, 5, 1] else ![0, 2, 1, 4, 3, 5, 6, 7])) else (if i.val < 11 then (if i.val < 10 then ![0, 2, 1, 4, 3, 5, 6, 7] else ![0, 2, 1, 4, 3, 5, 6, 7]) else (if i.val < 12 then ![0, 2, 1, 4, 3, 5, 6, 7] else ![0, 2, 1, 4, 3, 5, 6, 7]))))

set_option maxHeartbeats 1000000 in
private theorem left_checked : ∀ (i : Fin 13) (x : Fin 8),
    inverseImages i (images i x) = x := by decide +kernel
set_option maxHeartbeats 1000000 in
private theorem right_checked : ∀ (i : Fin 13) (x : Fin 8),
    images i (inverseImages i x) = x := by decide +kernel

def elements (i : Fin 13) : Ambient where
  toFun := images i
  invFun := inverseImages i
  left_inv := left_checked i
  right_inv := right_checked i

def sourceGenerators (i : Fin 13) : Fin 5 → Ambient :=
  Matrix.vecCons (representatives (S8Seed9NormalizerRoots.roots (indices i)))
    BinaryMenuCayley8T9.generators

def forwardWords (i : Fin 13) : Fin 4 → FiniteGeneratorWord (Fin 4) :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else (if i.val < 2 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)])) else (if i.val < 4 then ![(.generator 0), (.generator 1), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 3)] else (if i.val < 5 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)]))) else (if i.val < 9 then (if i.val < 7 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else (if i.val < 8 then ![(.generator 0), (.generator 1), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 3)] else ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)])) else (if i.val < 11 then (if i.val < 10 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)]) else (if i.val < 12 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)]))))

def backwardWords (i : Fin 13) : Fin 4 → FiniteGeneratorWord (Fin 4) :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else (if i.val < 2 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)])) else (if i.val < 4 then ![(.generator 0), (.generator 1), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 3)] else (if i.val < 5 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)]))) else (if i.val < 9 then (if i.val < 7 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else (if i.val < 8 then ![(.generator 0), (.generator 1), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 3)] else ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)])) else (if i.val < 11 then (if i.val < 10 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)]) else (if i.val < 12 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)] else ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 3)]))))

def inclusionWords (i : Fin 13) : FiniteGeneratorWord (Fin 5) :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (.mul (.mul (.generator 1) (.mul (.inv (.generator 3)) (.inv (.generator 2)))) (.mul (.mul (.inv (.generator 1)) (.inv (.generator 0))) (.mul (.generator 1) (.generator 0)))) else (if i.val < 2 then (.mul (.mul (.generator 1) (.mul (.inv (.generator 3)) (.inv (.generator 2)))) (.mul (.mul (.inv (.generator 1)) (.inv (.generator 0))) (.mul (.generator 1) (.generator 0)))) else (.mul (.mul (.generator 1) (.mul (.inv (.generator 3)) (.inv (.generator 2)))) (.mul (.generator 0) (.mul (.generator 3) (.inv (.generator 0))))))) else (if i.val < 4 then (.mul (.mul (.generator 1) (.inv (.generator 2))) (.mul (.generator 0) (.mul (.generator 3) (.inv (.generator 0))))) else (if i.val < 5 then (.mul (.mul (.generator 1) (.mul (.inv (.generator 3)) (.inv (.generator 4)))) (.mul (.generator 0) (.mul (.generator 1) (.inv (.generator 0))))) else (.mul (.mul (.generator 1) (.mul (.inv (.generator 3)) (.inv (.generator 2)))) (.mul (.mul (.inv (.generator 1)) (.generator 0)) (.mul (.generator 1) (.inv (.generator 0)))))))) else (if i.val < 9 then (if i.val < 7 then (.mul (.mul (.mul (.generator 1) (.inv (.generator 3))) (.mul (.inv (.generator 4)) (.generator 0))) (.mul (.mul (.generator 0) (.generator 3)) (.mul (.inv (.generator 0)) (.inv (.generator 0))))) else (if i.val < 8 then (.mul (.mul (.generator 1) (.inv (.generator 2))) (.mul (.generator 0) (.mul (.generator 2) (.inv (.generator 0))))) else (.mul (.mul (.generator 1) (.mul (.inv (.generator 3)) (.inv (.generator 2)))) (.mul (.inv (.generator 0)) (.mul (.generator 1) (.generator 0)))))) else (if i.val < 11 then (if i.val < 10 then (.mul (.mul (.generator 1) (.mul (.inv (.generator 3)) (.inv (.generator 4)))) (.mul (.generator 0) (.mul (.generator 3) (.generator 0)))) else (.mul (.mul (.generator 1) (.mul (.inv (.generator 3)) (.inv (.generator 4)))) (.mul (.mul (.inv (.generator 2)) (.generator 0)) (.mul (.generator 3) (.generator 0))))) else (if i.val < 12 then (.mul (.mul (.generator 1) (.mul (.inv (.generator 3)) (.inv (.generator 2)))) (.mul (.generator 0) (.mul (.generator 1) (.inv (.generator 0))))) else (.mul (.mul (.generator 1) (.inv (.generator 1))) (.mul (.generator 0) (.generator 0)))))))

set_option maxHeartbeats 1000000 in
private theorem forward_checked : ∀ (i : Fin 13) (j : Fin 4),
    (forwardWords i j).eval BinaryMenuCayley8T9.generators =
      (MulAut.conj (elements i)) (BinaryMenuCayley8T9.generators j) := by
  intro i j
  apply Equiv.ext
  intro x
  revert i j x
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem backward_checked : ∀ (i : Fin 13) (j : Fin 4),
    (backwardWords i j).eval BinaryMenuCayley8T9.generators =
      (MulAut.conj (elements i)).symm (BinaryMenuCayley8T9.generators j) := by
  intro i j
  apply Equiv.ext
  intro x
  revert i j x
  decide +kernel

def normalizerCertificate (i : Fin 13) :
    FiniteGeneratorEquivWordCertificate (MulAut.conj (elements i))
      BinaryMenuCayley8T9.generators BinaryMenuCayley8T9.generators where
  forward := { words := forwardWords i, equations := forward_checked i }
  backward := { words := backwardWords i, equations := backward_checked i }

set_option maxHeartbeats 1000000 in
private theorem powers_checked : ∀ i : Fin 13, elements i ^ (2 ^ 3) = 1 := by
  intro i
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem outside_checked : ∀ i : Fin 13, elements i ∉ H := by
  intro i
  change elements i ∉ Subgroup.closure (Set.range BinaryMenuCayley8T9.generators)
  rw [BinaryMenuCayley8T9.certificate.mem_closure_iff]
  revert i
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem inclusion_checked : ∀ i : Fin 13,
    (inclusionWords i).eval (sourceGenerators i) = elements i := by
  intro i
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def family : FiniteNormalizerExtensionWordFamily
    BinaryMenuCayley8T9.generators sourceGenerators 2 3 where
  elements := elements
  normalizer := normalizerCertificate
  power_eq_one := powers_checked
  outside_seed := outside_checked
  inclusionWords := inclusionWords
  inclusion_eq := inclusion_checked

theorem source_closure (i : Fin 13) :
    Subgroup.closure (Set.range (sourceGenerators i)) =
      H ⊔ Subgroup.closure {representatives (S8Seed9NormalizerRoots.roots (indices i))} := by
  simp only [sourceGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

abbrev extendedSeed (i : Fin 13) : Subgroup Ambient := family.extension i

theorem extended_isPGroup (i : Fin 13) : IsPGroup 2 (extendedSeed i) :=
  family.extension_isPGroup (IsPGroup.of_card (n := 4) BinaryMenuCayley8T9.exact_card) i

theorem extended_card_gt (i : Fin 13) : 16 < Nat.card (extendedSeed i) := by
  have h := family.card_lt_extension i
  rw [BinaryMenuCayley8T9.exact_card] at h
  exact h

theorem extended_le_adjoin (i : Fin 13) : extendedSeed i ≤
    H ⊔ Subgroup.closure {representatives (S8Seed9NormalizerRoots.roots (indices i))} := by
  have h := family.extension_le_source i (by rw [source_closure]; exact le_sup_left)
  rw [source_closure] at h
  exact h

end SymmetricSubgroupAsymptotics.S8Seed9HighChunk11
end
