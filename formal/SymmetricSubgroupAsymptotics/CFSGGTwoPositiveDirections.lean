import SymmetricSubgroupAsymptotics.CFSGGTwoWeylMonomial
import SymmetricSubgroupAsymptotics.CFSGGTwoPositivePGroup

/-! Six actual Weyl-conjugate positive directions, with their SAME inner
words and row-monomial coordinates. These are distinguished from the
positive SIMPLE-root closure; no bad-prime equality of those groups is
assumed. Strict support and normalizer arguments are separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoPositiveDirections
open CFSGGTwoSerreMatrices CFSGGTwoShortWeylMatrices CFSGGTwoWeylMonomial
open CFSGTypeAMonomialMatrices

def rootNode : Fin 6 → Fin 2 := ![0, 1, 0, 0, 1, 1]

def directionWord (K : Type) [Field K] : Fin 6 → (Mat K)ˣ :=
  ![1, 1, longWeyl K, shortWeyl K * longWeyl K,
    shortWeyl K, longWeyl K * shortWeyl K]

def directionPermutation : Fin 6 → Equiv.Perm Index :=
  ![1, 1, longPermutation, longPermutation * shortPermutation,
    shortPermutation, shortPermutation * longPermutation]

def directionWeight (K : Type) [Field K] (j : Fin 6) (x : Index) : K :=
  ![1, 1, longWeight K x, shortWeight K x * longWeight K (shortPermutation x),
    shortWeight K x, longWeight K x * shortWeight K (longPermutation x)] j

theorem directionWeight_ne_zero (K : Type) [Field K] (j : Fin 6) (x : Index) :
    directionWeight K j x ≠ 0 := by
  fin_cases j
  · exact one_ne_zero
  · exact one_ne_zero
  · exact longWeight_ne_zero K x
  · exact mul_ne_zero (shortWeight_ne_zero K x) (longWeight_ne_zero K (shortPermutation x))
  · exact shortWeight_ne_zero K x
  · exact mul_ne_zero (longWeight_ne_zero K x) (shortWeight_ne_zero K (longPermutation x))

theorem directionWord_monomial (K : Type) [Field K] (j : Fin 6) :
    (directionWord K j : Mat K) = monomial (directionPermutation j) (directionWeight K j) := by
  fin_cases j
  · change (1 : Mat K) = monomial 1 (fun _ => 1)
    ext x y
    simp [monomial_apply, Matrix.one_apply]
  · change (1 : Mat K) = monomial 1 (fun _ => 1)
    ext x y
    simp [monomial_apply, Matrix.one_apply]
  · exact longWeyl_monomial K
  · change (shortWeyl K : Mat K) * (longWeyl K : Mat K) =
      monomial (longPermutation * shortPermutation)
        (fun x => shortWeight K x * longWeight K (shortPermutation x))
    rw [shortWeyl_monomial, longWeyl_monomial, CFSGMonomialProductCoordinates.monomial_mul]
  · exact shortWeyl_monomial K
  · change (longWeyl K : Mat K) * (shortWeyl K : Mat K) =
      monomial (shortPermutation * longPermutation)
        (fun x => longWeight K x * shortWeight K (longPermutation x))
    rw [shortWeyl_monomial, longWeyl_monomial, CFSGMonomialProductCoordinates.monomial_mul]

theorem directionWord_mem (K : Type) [Field K] (j : Fin 6) :
    directionWord K j ∈ naturalGroup K := by
  have hs : shortWeyl K ∈ naturalGroup K := (naturalShortWeyl K).property
  have hl : longWeyl K ∈ naturalGroup K := (naturalLongWeyl K).property
  fin_cases j
  · exact (naturalGroup K).one_mem
  · exact (naturalGroup K).one_mem
  · exact hl
  · exact (naturalGroup K).mul_mem hs hl
  · exact hs
  · exact (naturalGroup K).mul_mem hl hs

def positiveRoot (K : Type) [Field K] (j : Fin 6) (t : K) : (Mat K)ˣ :=
  directionWord K j * rootTransvection K false (rootNode j) t * (directionWord K j)⁻¹

theorem positiveRoot_mem (K : Type) [Field K] (j : Fin 6) (t : K) :
    positiveRoot K j t ∈ naturalGroup K :=
  (naturalGroup K).mul_mem
    ((naturalGroup K).mul_mem (directionWord_mem K j) (naturalRoot K false (rootNode j) t).property)
    ((naturalGroup K).inv_mem (directionWord_mem K j))

def positiveGroup (K : Type) [Field K] : Subgroup ((Mat K)ˣ) :=
  Subgroup.closure (Set.range (fun z : Fin 6 × K => positiveRoot K z.1 z.2))

theorem positiveGroup_le_natural (K : Type) [Field K] : positiveGroup K ≤ naturalGroup K := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨z, rfl⟩
  exact positiveRoot_mem K z.1 z.2

theorem simple_positive_le (K : Type) [Field K] :
    CFSGGTwoPositivePGroup.rootGroup K false ≤ positiveGroup K := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i, t⟩, rfl⟩
  fin_cases i
  · apply Subgroup.subset_closure
    refine ⟨(0, t), ?_⟩
    simp [positiveRoot, directionWord, rootNode]
  · apply Subgroup.subset_closure
    refine ⟨(1, t), ?_⟩
    simp [positiveRoot, directionWord, rootNode]

end SymmetricSubgroupAsymptotics.CFSGGTwoPositiveDirections
