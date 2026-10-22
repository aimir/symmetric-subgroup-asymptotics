import SymmetricSubgroupAsymptotics.CFSGAlternatingCyclicDoubleSwap
import SymmetricSubgroupAsymptotics.CFSGDihedralTwoGroupWords
import SymmetricSubgroupAsymptotics.CFSGOddConjugateSubgroupExtraction
import Mathlib.GroupTheory.Sylow

/-! Two actual conjugate Sylow two-subgroups generate the alternating
group on `4*k+1` points, for `k≥2`. The chosen Sylow contains the explicit
even reflection and the adjacent double transposition. Normalizer
solubility is a separate obligation and is not asserted here. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingCyclicSylowGeneration
open CFSGAlternatingCyclicReflection CFSGAlternatingCyclicDoubleSwap
open CFSGPermutationCrossSwapWords

theorem adjacentDoubleSwap_square (k : ℕ) (hk : 2 ≤ k) :
    adjacentDoubleSwap k ^ 2 = 1 := by
  have hf := coordinates_injective k hk
  apply doubleSwap_square
  · exact fun h => (by decide : (0 : Fin 7) ≠ 2) (hf h)
  · exact fun h => (by decide : (0 : Fin 7) ≠ 3) (hf h)
  · exact fun h => (by decide : (1 : Fin 7) ≠ 2) (hf h)
  · exact fun h => (by decide : (1 : Fin 7) ≠ 3) (hf h)

theorem adjacentDoubleSwap_commute_reflection (k : ℕ) (hk : 2 ≤ k) :
    Commute (adjacentDoubleSwap k) (reflection k) := by
  have hf := coordinates_injective k hk
  have hd : [coordinates k 0, coordinates k 1, coordinates k 2, coordinates k 3].Nodup := by
    simpa only [List.map_cons, List.map_nil] using
      (List.Nodup.map hf (by decide : ([0, 1, 2, 3] : List (Fin 7)).Nodup))
  have hs := (Equiv.Perm.disjoint_swap_swap hd).commute
  have hc : reflection k * adjacentDoubleSwap k * (reflection k)⁻¹ =
      adjacentDoubleSwap k := by
    rw [show adjacentDoubleSwap k = doubleSwap (0 : Cycle k) 1 2 3 from rfl,
      CFSGAlternatingDoubleSwapGeneration.conjugate_doubleSwap]
    have h0 : reflection k (0 : Cycle k) = 3 := by rw [reflection_apply]; ring
    have h1 : reflection k (1 : Cycle k) = 2 := by rw [reflection_apply]; ring
    have h2 : reflection k (2 : Cycle k) = 1 := by rw [reflection_apply]; ring
    have h3 : reflection k (3 : Cycle k) = 0 := by rw [reflection_apply]; ring
    rw [h0, h1, h2, h3]
    change Equiv.swap (3 : Cycle k) 2 * Equiv.swap 1 0 =
      Equiv.swap 0 1 * Equiv.swap 2 3
    rw [Equiv.swap_comm (3 : Cycle k) 2, Equiv.swap_comm (1 : Cycle k) 0]
    exact hs.eq.symm
  exact ((mul_inv_eq_iff_eq_mul).mp hc).symm

abbrev A (k : ℕ) := alternatingGroup (Cycle k)

def rotationElement (k : ℕ) : A k :=
  ⟨rotation k, Equiv.Perm.mem_alternatingGroup.mpr (rotation_even k)⟩

def reflectionElement (k : ℕ) : A k :=
  ⟨reflection k, Equiv.Perm.mem_alternatingGroup.mpr (reflection_even k)⟩

def doubleSwapElement (k : ℕ) (hk : 2 ≤ k) : A k :=
  ⟨adjacentDoubleSwap k, adjacentDoubleSwap_even k (by omega)⟩

theorem seed_isPGroup (k : ℕ) (hk : 2 ≤ k) :
    IsPGroup 2 (Subgroup.closure
      ({reflectionElement k, (1 : A k), doubleSwapElement k hk} : Set (A k))) := by
  apply CFSGDihedralTwoGroupWords.closure_three_involutions_isPGroup
  · exact Subtype.ext (reflection_square k)
  · simp
  · exact Subtype.ext (adjacentDoubleSwap_square k hk)
  · change (reflectionElement k * 1) ^ 4 = 1
    rw [mul_one, show (4 : ℕ) = 2 * 2 by decide, pow_mul]
    have h : reflectionElement k ^ 2 = 1 := Subtype.ext (reflection_square k)
    rw [h, one_pow]
  · exact Subtype.ext (adjacentDoubleSwap_commute_reflection k hk).eq
  · exact Commute.one_right _

theorem exists_sylow_two_conjugates_generate (k : ℕ) (hk : 2 ≤ k) :
    ∃ P : Sylow 2 (A k),
      Subgroup.closure ((P : Set (A k)) ∪
        (P : Subgroup (A k)).map (MulAut.conj (rotationElement k)).toMonoidHom) = ⊤ := by
  obtain ⟨P, hP⟩ := (seed_isPGroup k hk).exists_le_sylow
  refine ⟨P, ?_⟩
  have hp : reflectionElement k ∈ P := hP (Subgroup.subset_closure (by simp))
  have ha : doubleSwapElement k hk ∈ P := hP (Subgroup.subset_closure (by simp))
  let K := Subgroup.closure ((P : Set (A k)) ∪
    (P : Subgroup (A k)).map (MulAut.conj (rotationElement k)).toMonoidHom)
  have hg : rotationElement k ∈ K := by
    apply CFSGOddConjugateSubgroupExtraction.odd_element_mem_two_conjugates
      (P : Subgroup (A k)) (reflectionElement k) (rotationElement k) (2 * k) hp
    · exact Subtype.ext (reflection_square k)
    · exact Subtype.ext (reflection_inverts k)
    · apply Subtype.ext
      change rotation k ^ (2 * (2 * k) + 1) = 1
      simpa only [show 2 * (2 * k) + 1 = 4 * k + 1 by omega] using rotation_odd_power k
  have haK : doubleSwapElement k hk ∈ K := Subgroup.subset_closure (Or.inl ha)
  let L : Subgroup (Equiv.Perm (Cycle k)) := K.map (alternatingGroup (Cycle k)).subtype
  have hfull : alternatingGroup (Cycle k) ≤ L := by
    apply alternating_le_of_rotation_doubleSwap k hk L
    · exact ⟨rotationElement k, hg, rfl⟩
    · exact ⟨doubleSwapElement k hk, haK, rfl⟩
  apply (Subgroup.eq_top_iff' K).mpr
  intro x
  obtain ⟨y, hy, he⟩ := hfull x.property
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

end SymmetricSubgroupAsymptotics.CFSGAlternatingCyclicSylowGeneration
