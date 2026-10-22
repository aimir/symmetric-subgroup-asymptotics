import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWordNormalizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementNormalizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWeylAction

/-! A literal Weyl word normalizing the excluded-simple complement lies
in N(U), or becomes an element of N(U) after multiplication by the one
excluded simple Weyl element. No diagonal-word/torus identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementWord
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckColumns
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveComplement
open CFSGNormTwoGeckComplementNormalizer CFSGNormTwoCoordinateComplementRoots
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootWeylAction
open CFSGNormTwoCoordinatePositiveWordNormalizer CFSGIntegralNormTwoSigns
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "U" => rootGroup A hs hp b₀ s₀ K false
local notation "M" => positiveComplement A hs hp b₀ s₀ K

theorem complement_word_positive (i : Fin r) (w : List (Fin r))
    (hw : wordUnit A hs hp b₀ s₀ K w∈Subgroup.normalizer (M i : Set _))
    (k : Roots A) (hk : ∀j,0≤k.val j) (hki : k≠(s₀ i : Roots A)) :
    ∀j,0≤(wordRoot A hs hp b₀ s₀ w k).val j := by
  have hroot := (rootSubgroup_le_complement_iff A hd hs hp ho K i k).mpr ⟨hk,hki⟩
  have hmap : (rootSubgroup A hd hs hp ho K k).map
      (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom≤M i := by
    rintro x ⟨y,hy,rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hw y).mp (hroot hy)
  rw [word_eq_canonicalWord,rootSubgroup_map_word] at hmap
  exact ((rootSubgroup_le_complement_iff A hd hs hp ho K i
    (wordRoot A hs hp b₀ s₀ w k)).mp hmap).1

private theorem simple_positive (j : Fin r) : ∀t,0≤(s₀ j : Roots A).val t := by
  intro t
  change 0≤(Pi.single j (1:ℤ) : Fin r→ℤ) t
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

theorem complement_word_normalizer_dichotomy (i : Fin r) (w : List (Fin r))
    (hw : wordUnit A hs hp b₀ s₀ K w∈Subgroup.normalizer (M i : Set _)) :
    wordUnit A hs hp b₀ s₀ K w∈Subgroup.normalizer (U : Set _) ∨
      wordUnit A hs hp b₀ s₀ K (w++[i])∈Subgroup.normalizer (U : Set _) := by
  have hother (v : List (Fin r))
      (hv : wordUnit A hs hp b₀ s₀ K v∈Subgroup.normalizer (M i : Set _))
      (j : Fin r) (hji : j≠i) : ∀t,0≤(wordRoot A hs hp b₀ s₀ v (s₀ j)).val t := by
    apply complement_word_positive A hd hs hp ho K i v hv (s₀ j)
      (simple_positive A hd hs hp ho j)
    intro h
    exact hji ((s₀).injective (Subtype.ext h))
  let k := wordRoot A hs hp b₀ s₀ w (s₀ i)
  rcases norm_two_coordinates_one_sign A hs hp (fun j=>by rw [hd j];exact even_two)
    ho k.val k.property with hpos|hneg
  · left
    apply positive_word_mem_normalizer A hd hs hp ho K w
    intro j t
    by_cases hji : j=i
    · subst j
      exact hpos t
    · exact hother w hw j hji t
  · right
    let NM : Subgroup (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ :=
      Subgroup.normalizer (M i : Set _)
    have hwi : canonicalWeyl D K i∈NM := weyl_mem_normalizer A hs hp b₀ s₀ K i
    have hw' : wordUnit A hs hp b₀ s₀ K (w++[i])∈NM := by
      rw [wordUnit_append]
      simpa only [wordUnit,mul_one] using NM.mul_mem hw hwi
    apply positive_word_mem_normalizer A hd hs hp ho K (w++[i])
    intro j t
    by_cases hji : j=i
    · subst j
      rw [wordRoot_append]
      change 0≤(wordRoot A hs hp b₀ s₀ w (negativeIndex A hs hp (s₀ i))).val t
      rw [wordRoot_negative_val]
      change 0≤ -k.val t
      exact neg_nonneg.mpr (hneg t)
    · exact hother (w++[i]) hw' j hji t

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementWord
