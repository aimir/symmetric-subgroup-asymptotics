import SymmetricSubgroupAsymptotics.CFSGAlternatingCyclicSylowGeneration
import SymmetricSubgroupAsymptotics.CFSGAlternatingSumSupport

/-! A literal Sylow seed connecting two outsider points to the long cycle.
The reflection interchanges cycle points `4` and `−1`; the crossing double
swap has dihedral product exponent four with it and commutes with (01)(23).
All three generators are actual even permutations of the original sum. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingCrossSeed
open CFSGAlternatingCyclicReflection CFSGAlternatingCyclicDoubleSwap
open CFSGAlternatingSumSupport CFSGPermutationCrossSwapWords

abbrev X (k r : ℕ) := Cycle k ⊕ Fin r

def p (k r : ℕ) : Equiv.Perm (X k r) := extensionHom (Cycle k) r (reflection k)
def a (k r : ℕ) : Equiv.Perm (X k r) := extensionHom (Cycle k) r (adjacentDoubleSwap k)
def g (k r : ℕ) : Equiv.Perm (X k r) := extensionHom (Cycle k) r (rotation k)

def q (k r : ℕ) (hr : 2 ≤ r) : Equiv.Perm (X k r) :=
  doubleSwap (Sum.inl 4) (Sum.inr ⟨0, by omega⟩)
    (Sum.inl (-1)) (Sum.inr ⟨1, by omega⟩)

theorem first_ne_four (k : ℕ) (hk : 2 ≤ k) (i : Fin 4) :
    (i.val : Cycle k) ≠ 4 := by
  intro h
  have hv := congrArg ZMod.val h
  change (i.val : Cycle k).val = ((4 : ℕ) : Cycle k).val at hv
  rw [ZMod.val_natCast_of_lt (show i.val < 4 * k + 1 by omega),
    ZMod.val_natCast_of_lt (show 4 < 4 * k + 1 by omega)] at hv
  omega

theorem first_ne_neg_one (k : ℕ) (hk : 2 ≤ k) (i : Fin 4) :
    (i.val : Cycle k) ≠ -1 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (show i.val < 4 * k + 1 by omega),
    ZMod.val_neg_one] at hv
  omega

theorem four_ne_neg_one (k : ℕ) (hk : 2 ≤ k) : (4 : Cycle k) ≠ -1 := by
  intro h
  have hv := congrArg ZMod.val h
  change ((4 : ℕ) : Cycle k).val = (-1 : Cycle k).val at hv
  rw [ZMod.val_natCast_of_lt (show 4 < 4 * k + 1 by omega), ZMod.val_neg_one] at hv
  omega

theorem a_fix_four (k r : ℕ) (hk : 2 ≤ k) : a k r (Sum.inl 4) = Sum.inl 4 := by
  have hn : ∀ i : Fin 4, (4 : Cycle k) ≠ i.val :=
    fun i => Ne.symm (first_ne_four k hk i)
  have h40 : (4 : Cycle k) ≠ 0 := by simpa using hn 0
  have h41 : (4 : Cycle k) ≠ 1 := by simpa using hn 1
  have h42 : (4 : Cycle k) ≠ 2 := by simpa using hn 2
  have h43 : (4 : Cycle k) ≠ 3 := by simpa using hn 3
  simp [a, adjacentDoubleSwap, doubleSwap, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    h40, h41, h42, h43]

theorem a_fix_neg_one (k r : ℕ) (hk : 2 ≤ k) : a k r (Sum.inl (-1)) = Sum.inl (-1) := by
  have hn : ∀ i : Fin 4, (-1 : Cycle k) ≠ i.val :=
    fun i => Ne.symm (first_ne_neg_one k hk i)
  have hm0 : (-1 : Cycle k) ≠ 0 := by simpa using hn 0
  have hm1 : (-1 : Cycle k) ≠ 1 := by simpa using hn 1
  have hm2 : (-1 : Cycle k) ≠ 2 := by simpa using hn 2
  have hm3 : (-1 : Cycle k) ≠ 3 := by simpa using hn 3
  simp [a, adjacentDoubleSwap, doubleSwap, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    hm0, hm1, hm2, hm3]

theorem a_commute_q (k r : ℕ) (hk : 2 ≤ k) (hr : 2 ≤ r) : Commute (a k r) (q k r hr) := by
  apply Equiv.Perm.Disjoint.commute
  intro x
  cases x with
  | inr i => exact Or.inl rfl
  | inl x =>
      by_cases h4 : x = 4
      · subst x; exact Or.inl (a_fix_four k r hk)
      by_cases hm : x = -1
      · subst x; exact Or.inl (a_fix_neg_one k r hk)
      right
      simp [q, doubleSwap, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h4, hm]

theorem q_square (k r : ℕ) (hk : 2 ≤ k) (hr : 2 ≤ r) : q k r hr ^ 2 = 1 := by
  apply doubleSwap_square
  · exact fun h => four_ne_neg_one k hk (Sum.inl_injective h)
  · intro h; cases h
  · intro h; cases h
  · intro h
    have he := congrArg Fin.val (Sum.inr_injective h)
    change (0 : ℕ) = 1 at he
    omega

theorem p_q_fourth (k r : ℕ) (hk : 2 ≤ k) (hr : 2 ≤ r) : (p k r * q k r hr) ^ 4 = 1 := by
  apply involution_cross_rotation_pow_four
  · change extensionHom (Cycle k) r (reflection k) ^ 2 = 1
    rw [← map_pow, reflection_square, map_one]
  · change Sum.inl (reflection k 4) = Sum.inl (-1)
    congr 1
    rw [reflection_apply]
    ring
  · change Sum.inl (reflection k (-1)) = Sum.inl 4
    congr 1
    rw [reflection_apply]
    ring
  · rfl
  · rfl
  · exact fun h => four_ne_neg_one k hk (Sum.inl_injective h)
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h
    have he := congrArg Fin.val (Sum.inr_injective h)
    change (0 : ℕ) = 1 at he
    omega

theorem seed_isPGroup (k r : ℕ) (hk : 2 ≤ k) (hr : 2 ≤ r) :
    IsPGroup 2 (Subgroup.closure ({p k r, q k r hr, a k r} : Set (Equiv.Perm (X k r)))) := by
  apply CFSGDihedralTwoGroupWords.closure_three_involutions_isPGroup
  · change extensionHom (Cycle k) r (reflection k) ^ 2 = 1
    rw [← map_pow, reflection_square, map_one]
  · exact q_square k r hk hr
  · change extensionHom (Cycle k) r (adjacentDoubleSwap k) ^ 2 = 1
    rw [← map_pow, CFSGAlternatingCyclicSylowGeneration.adjacentDoubleSwap_square k hk, map_one]
  · exact p_q_fourth k r hk hr
  · exact (CFSGAlternatingCyclicSylowGeneration.adjacentDoubleSwap_commute_reflection k hk).map
      (extensionHom (Cycle k) r)
  · exact a_commute_q k r hk hr

theorem seed_le_alternating (k r : ℕ) (hk : 2 ≤ k) (hr : 2 ≤ r) :
    Subgroup.closure ({p k r, q k r hr, a k r} : Set (Equiv.Perm (X k r))) ≤
      alternatingGroup (X k r) := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx
  · subst x
    exact extension_even (Cycle k) r (reflection k)
      (Equiv.Perm.mem_alternatingGroup.mpr (reflection_even k))
  · subst x
    apply Equiv.Perm.mem_alternatingGroup.mpr
    change Equiv.Perm.sign (Equiv.swap (Sum.inl (4 : Cycle k)) (Sum.inr (⟨0, by omega⟩ : Fin r)) *
      Equiv.swap (Sum.inl (-1 : Cycle k)) (Sum.inr (⟨1, by omega⟩ : Fin r))) = 1
    rw [map_mul, Equiv.Perm.sign_swap (by intro h; cases h),
      Equiv.Perm.sign_swap (by intro h; cases h)]
    norm_num
  · subst x
    exact extension_even (Cycle k) r (adjacentDoubleSwap k) (adjacentDoubleSwap_even k (by omega))

theorem exists_sylow_seed (k r : ℕ) (hk : 2 ≤ k) (hr : 2 ≤ r) :
    ∃ P : Sylow 2 (alternatingGroup (X k r)),
      Subgroup.closure ({p k r, q k r hr, a k r} : Set (Equiv.Perm (X k r))) ≤
        (P : Subgroup (alternatingGroup (X k r))).map (alternatingGroup (X k r)).subtype := by
  let H := Subgroup.closure ({p k r, q k r hr, a k r} : Set (Equiv.Perm (X k r)))
  have hH := seed_isPGroup k r hk hr
  have heven : H ≤ alternatingGroup (X k r) := seed_le_alternating k r hk hr
  obtain ⟨P, hP⟩ := (hH.comap_of_injective (alternatingGroup (X k r)).subtype
    (alternatingGroup (X k r)).subtype_injective).exists_le_sylow
  refine ⟨P, ?_⟩
  intro x hx
  exact ⟨⟨x, heven hx⟩, hP hx, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGAlternatingCrossSeed
