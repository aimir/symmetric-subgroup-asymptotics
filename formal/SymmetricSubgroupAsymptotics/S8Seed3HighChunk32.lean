import SymmetricSubgroupAsymptotics.S8Seed3NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteNormalizerExtensionWordFamily
import Mathlib.Data.Fin.VecNotation

/-! One selected bounded family of actual larger binary extensions.
All ordinary words, power equations, seed nonmembership and permutation
coordinates are checked by Lean's kernel. No root-order flag is input. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed3HighChunk32
open S8Seed3LeftCosets

def indices : Fin 13 → Fin 484 := ![460, 462, 464, 466, 467, 468, 469, 472, 473, 475, 477, 479, 480]

def images (i : Fin 13) : Fin 8 → Fin 8 :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ![1, 0, 2, 5, 3, 6, 4, 7] else (if i.val < 2 then ![0, 2, 1, 6, 5, 3, 4, 7] else ![2, 3, 6, 1, 0, 5, 4, 7])) else (if i.val < 4 then ![2, 1, 0, 5, 4, 3, 6, 7] else (if i.val < 5 then ![7, 1, 2, 4, 3, 5, 6, 0] else ![7, 3, 1, 4, 2, 6, 0, 5]))) else (if i.val < 9 then (if i.val < 7 then ![7, 3, 4, 1, 2, 6, 5, 0] else (if i.val < 8 then ![4, 5, 2, 3, 0, 1, 6, 7] else ![5, 4, 0, 2, 6, 3, 7, 1])) else (if i.val < 11 then (if i.val < 10 then ![4, 2, 5, 3, 0, 6, 1, 7] else ![2, 4, 5, 0, 1, 3, 6, 7]) else (if i.val < 12 then ![5, 4, 0, 2, 6, 3, 7, 1] else ![4, 0, 3, 2, 5, 1, 6, 7]))))

def inverseImages (i : Fin 13) : Fin 8 → Fin 8 :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ![1, 0, 2, 4, 6, 3, 5, 7] else (if i.val < 2 then ![0, 2, 1, 5, 6, 4, 3, 7] else ![4, 3, 0, 1, 6, 5, 2, 7])) else (if i.val < 4 then ![2, 1, 0, 5, 4, 3, 6, 7] else (if i.val < 5 then ![7, 1, 2, 4, 3, 5, 6, 0] else ![6, 2, 4, 1, 3, 7, 5, 0]))) else (if i.val < 9 then (if i.val < 7 then ![7, 3, 4, 1, 2, 6, 5, 0] else (if i.val < 8 then ![4, 5, 2, 3, 0, 1, 6, 7] else ![2, 7, 3, 5, 1, 0, 4, 6])) else (if i.val < 11 then (if i.val < 10 then ![4, 6, 1, 3, 0, 2, 5, 7] else ![3, 4, 0, 5, 1, 2, 6, 7]) else (if i.val < 12 then ![2, 7, 3, 5, 1, 0, 4, 6] else ![1, 5, 3, 2, 0, 4, 6, 7]))))

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

def sourceGenerators (i : Fin 13) : Fin 4 → Ambient :=
  Matrix.vecCons (representatives (S8Seed3NormalizerRoots.roots (indices i)))
    BinaryMenuCayley8T3.generators

def forwardWords (i : Fin 13) : Fin 3 → FiniteGeneratorWord (Fin 3) :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ![(.generator 1), (.generator 0), (.mul (.generator 1) (.generator 2))] else (if i.val < 2 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.mul (.generator 1) (.generator 2)))] else ![(.mul (.generator 0) (.generator 1)), (.generator 2), (.generator 1)])) else (if i.val < 4 then ![(.mul (.generator 0) (.generator 1)), (.generator 1), (.mul (.generator 1) (.generator 2))] else (if i.val < 5 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.generator 2)] else ![(.mul (.generator 1) (.generator 2)), (.generator 1), (.mul (.generator 0) (.generator 1))]))) else (if i.val < 9 then (if i.val < 7 then ![(.generator 0), (.mul (.generator 0) (.generator 2)), (.mul (.generator 0) (.generator 1))] else (if i.val < 8 then ![(.mul (.generator 0) (.generator 2)), (.mul (.generator 1) (.generator 2)), (.generator 2)] else ![(.generator 2), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 0)])) else (if i.val < 11 then (if i.val < 10 then ![(.mul (.generator 0) (.generator 2)), (.mul (.generator 0) (.generator 1)), (.generator 2)] else ![(.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 0)]) else (if i.val < 12 then ![(.generator 2), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 0)] else ![(.mul (.generator 0) (.generator 2)), (.generator 0), (.mul (.generator 0) (.generator 1))]))))

def backwardWords (i : Fin 13) : Fin 3 → FiniteGeneratorWord (Fin 3) :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ![(.generator 1), (.generator 0), (.mul (.generator 0) (.generator 2))] else (if i.val < 2 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.mul (.generator 1) (.generator 2))] else ![(.mul (.generator 0) (.generator 2)), (.generator 2), (.generator 1)])) else (if i.val < 4 then ![(.mul (.generator 0) (.generator 1)), (.generator 1), (.mul (.generator 1) (.generator 2))] else (if i.val < 5 then ![(.generator 0), (.mul (.generator 0) (.generator 1)), (.generator 2)] else ![(.mul (.generator 1) (.generator 2)), (.generator 1), (.mul (.generator 0) (.generator 1))]))) else (if i.val < 9 then (if i.val < 7 then ![(.generator 0), (.mul (.generator 0) (.generator 2)), (.mul (.generator 0) (.generator 1))] else (if i.val < 8 then ![(.mul (.generator 0) (.generator 2)), (.mul (.generator 1) (.generator 2)), (.generator 2)] else ![(.generator 2), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 0)])) else (if i.val < 11 then (if i.val < 10 then ![(.mul (.generator 0) (.generator 2)), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 2)] else ![(.generator 2), (.mul (.generator 0) (.generator 2)), (.mul (.generator 1) (.generator 2))]) else (if i.val < 12 then ![(.generator 2), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 0)] else ![(.generator 1), (.mul (.generator 1) (.generator 2)), (.mul (.generator 0) (.generator 1))]))))

def inclusionWords (i : Fin 13) : FiniteGeneratorWord (Fin 4) :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (.mul (.generator 1) (.generator 0)) else (if i.val < 2 then (.mul (.generator 1) (.generator 0)) else (.mul (.generator 1) (.generator 0)))) else (if i.val < 4 then (.mul (.generator 1) (.generator 0)) else (if i.val < 5 then (.mul (.mul (.generator 1) (.mul (.inv (.generator 3)) (.inv (.generator 1)))) (.mul (.generator 0) (.mul (.generator 1) (.inv (.generator 0))))) else (.mul (.mul (.generator 1) (.inv (.generator 2))) (.mul (.generator 0) (.mul (.generator 1) (.inv (.generator 0)))))))) else (if i.val < 9 then (if i.val < 7 then (.mul (.mul (.generator 1) (.inv (.generator 2))) (.mul (.generator 0) (.generator 0))) else (if i.val < 8 then (.mul (.generator 1) (.generator 0)) else (.mul (.mul (.generator 1) (.mul (.inv (.generator 3)) (.inv (.generator 1)))) (.mul (.generator 0) (.mul (.generator 2) (.inv (.generator 0))))))) else (if i.val < 11 then (if i.val < 10 then (.mul (.generator 1) (.generator 0)) else (.mul (.generator 1) (.generator 0))) else (if i.val < 12 then (.mul (.generator 1) (.generator 0)) else (.mul (.generator 1) (.generator 0))))))

set_option maxHeartbeats 1000000 in
private theorem forward_checked : ∀ (i : Fin 13) (j : Fin 3),
    (forwardWords i j).eval BinaryMenuCayley8T3.generators =
      (MulAut.conj (elements i)) (BinaryMenuCayley8T3.generators j) := by
  intro i j
  apply Equiv.ext
  intro x
  revert i j x
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem backward_checked : ∀ (i : Fin 13) (j : Fin 3),
    (backwardWords i j).eval BinaryMenuCayley8T3.generators =
      (MulAut.conj (elements i)).symm (BinaryMenuCayley8T3.generators j) := by
  intro i j
  apply Equiv.ext
  intro x
  revert i j x
  decide +kernel

def normalizerCertificate (i : Fin 13) :
    FiniteGeneratorEquivWordCertificate (MulAut.conj (elements i))
      BinaryMenuCayley8T3.generators BinaryMenuCayley8T3.generators where
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
  change elements i ∉ Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)
  rw [BinaryMenuCayley8T3.certificate.mem_closure_iff]
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
    BinaryMenuCayley8T3.generators sourceGenerators 2 3 where
  elements := elements
  normalizer := normalizerCertificate
  power_eq_one := powers_checked
  outside_seed := outside_checked
  inclusionWords := inclusionWords
  inclusion_eq := inclusion_checked

theorem source_closure (i : Fin 13) :
    Subgroup.closure (Set.range (sourceGenerators i)) =
      H ⊔ Subgroup.closure {representatives (S8Seed3NormalizerRoots.roots (indices i))} := by
  simp only [sourceGenerators, Matrix.range_cons, Subgroup.closure_union, sup_comm]

abbrev extendedSeed (i : Fin 13) : Subgroup Ambient := family.extension i

theorem extended_isPGroup (i : Fin 13) : IsPGroup 2 (extendedSeed i) :=
  family.extension_isPGroup (IsPGroup.of_card (n := 3) BinaryMenuCayley8T3.exact_card) i

theorem extended_card_gt (i : Fin 13) : 8 < Nat.card (extendedSeed i) := by
  have h := family.card_lt_extension i
  rw [BinaryMenuCayley8T3.exact_card] at h
  exact h

theorem extended_le_adjoin (i : Fin 13) : extendedSeed i ≤
    H ⊔ Subgroup.closure {representatives (S8Seed3NormalizerRoots.roots (indices i))} := by
  have h := family.extension_le_source i (by rw [source_closure]; exact le_sup_left)
  rw [source_closure] at h
  exact h

end SymmetricSubgroupAsymptotics.S8Seed3HighChunk32
end
