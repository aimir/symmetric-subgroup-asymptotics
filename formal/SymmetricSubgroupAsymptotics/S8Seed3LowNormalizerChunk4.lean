import SymmetricSubgroupAsymptotics.S8Seed3NormalizerRoots
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate

/-! Selected literal low adjunctions lie in the SAME regularE8 normalizer.
Only bidirectional conjugation words enter the proof; low orders do not. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.S8Seed3LowNormalizerChunk4
open S8Seed3LeftCosets

def indices : Fin 12 → Fin 484 := ![456, 457, 458, 461, 463, 465, 470, 471, 474, 476, 478, 483]
def elements (i : Fin 12) : Ambient := representatives (S8Seed3NormalizerRoots.roots (indices i))
def forwardWords (i : Fin 12) : Fin 3 → FiniteGeneratorWord (Fin 3) := (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ![(.generator 1), (.mul (.generator 0) (.generator 1)), (.generator 2)] else (if i.val < 2 then ![(.mul (.generator 0) (.generator 1)), (.generator 0), (.mul (.generator 0) (.mul (.generator 1) (.generator 2)))] else ![(.mul (.generator 0) (.generator 1)), (.generator 0), (.generator 2)])) else (if i.val < 4 then ![(.generator 1), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.mul (.generator 1) (.generator 2)))] else (if i.val < 5 then ![(.mul (.generator 1) (.generator 2)), (.generator 2), (.mul (.generator 0) (.mul (.generator 1) (.generator 2)))] else ![(.mul (.generator 0) (.generator 2)), (.generator 2), (.mul (.generator 0) (.mul (.generator 1) (.generator 2)))]))) else (if i.val < 9 then (if i.val < 7 then ![(.generator 2), (.mul (.generator 0) (.generator 2)), (.mul (.generator 0) (.mul (.generator 1) (.generator 2)))] else (if i.val < 8 then ![(.generator 2), (.mul (.generator 1) (.generator 2)), (.mul (.generator 0) (.mul (.generator 1) (.generator 2)))] else ![(.mul (.generator 0) (.generator 2)), (.mul (.generator 0) (.generator 1)), (.generator 0)])) else (if i.val < 10 then ![(.mul (.generator 1) (.generator 2)), (.mul (.generator 0) (.generator 2)), (.generator 0)] else (if i.val < 11 then ![(.mul (.generator 0) (.generator 2)), (.generator 2), (.mul (.generator 1) (.generator 2))] else ![(.mul (.generator 0) (.generator 2)), (.generator 0), (.mul (.generator 1) (.generator 2))]))))
def backwardWords (i : Fin 12) : Fin 3 → FiniteGeneratorWord (Fin 3) := (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then ![(.mul (.generator 0) (.generator 1)), (.generator 0), (.generator 2)] else (if i.val < 2 then ![(.generator 1), (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2))] else ![(.generator 1), (.mul (.generator 0) (.generator 1)), (.generator 2)])) else (if i.val < 4 then ![(.mul (.generator 0) (.generator 1)), (.generator 0), (.mul (.generator 1) (.generator 2))] else (if i.val < 5 then ![(.mul (.generator 0) (.generator 2)), (.mul (.generator 0) (.generator 1)), (.generator 1)] else ![(.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.generator 2)), (.generator 1)]))) else (if i.val < 9 then (if i.val < 7 then ![(.mul (.generator 0) (.generator 1)), (.mul (.generator 1) (.generator 2)), (.generator 0)] else (if i.val < 8 then ![(.mul (.generator 1) (.generator 2)), (.mul (.generator 0) (.generator 1)), (.generator 0)] else ![(.generator 2), (.mul (.generator 1) (.generator 2)), (.mul (.generator 0) (.generator 2))])) else (if i.val < 10 then ![(.generator 2), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.mul (.generator 1) (.generator 2))] else (if i.val < 11 then ![(.mul (.generator 0) (.generator 1)), (.mul (.generator 1) (.generator 2)), (.generator 1)] else ![(.generator 1), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.mul (.generator 0) (.generator 1))]))))

set_option maxHeartbeats 1000000 in
private theorem forward_checked : ∀ (i : Fin 12) (j : Fin 3) (x : Fin 8),
    (forwardWords i j).eval BinaryMenuCayley8T3.generators x =
      (MulAut.conj (elements i)) (BinaryMenuCayley8T3.generators j) x := by decide +kernel
set_option maxHeartbeats 1000000 in
private theorem backward_checked : ∀ (i : Fin 12) (j : Fin 3) (x : Fin 8),
    (backwardWords i j).eval BinaryMenuCayley8T3.generators x =
      (MulAut.conj (elements i)).symm (BinaryMenuCayley8T3.generators j) x := by decide +kernel

def certificate (i : Fin 12) : FiniteGeneratorEquivWordCertificate
    (MulAut.conj (elements i)) BinaryMenuCayley8T3.generators BinaryMenuCayley8T3.generators where
  forward := { words := forwardWords i, equations := fun j => Equiv.ext (forward_checked i j) }
  backward := { words := backwardWords i, equations := fun j => Equiv.ext (backward_checked i j) }

theorem normalizes_seed (i : Fin 12) : elements i ∈ Subgroup.normalizer H := by
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  exact congrArg (fun K : Subgroup Ambient => (K : Set Ambient)) (certificate i).map_closure_eq

theorem adjoin_le_normalizer (i : Fin 12) :
    H ⊔ Subgroup.closure {representatives (S8Seed3NormalizerRoots.roots (indices i))} ≤
      Subgroup.normalizer H := by
  refine sup_le Subgroup.le_normalizer ((Subgroup.closure_le _).mpr ?_)
  intro g hg
  rcases Set.mem_singleton_iff.mp hg with rfl
  exact normalizes_seed i

end SymmetricSubgroupAsymptotics.S8Seed3LowNormalizerChunk4
end
