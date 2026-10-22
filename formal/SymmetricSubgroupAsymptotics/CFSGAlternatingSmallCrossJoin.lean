import SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossWords

/-! The actual length-five cross seed supplies the full supported alternating
group in the same two-conjugate Sylow join. No subgroup identification or
transitivity assumption is used until the final explicit action consumer. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossJoin
open CFSGAlternatingCyclicReflection CFSGAlternatingCyclicDoubleSwap CFSGAlternatingSumSupport
open CFSGAlternatingCrossSeed CFSGAlternatingCrossJoin

theorem exists_sylow_seed (r : ℕ) (hr : 2 ≤ r) :
    ∃ P : Sylow 2 (Alt 1 r),
      Subgroup.closure ({CFSGAlternatingSmallCrossSeed.p r,
        CFSGAlternatingSmallCrossSeed.q r hr, CFSGAlternatingSmallCrossSeed.b r hr} :
        Set (Equiv.Perm (X 1 r))) ≤
        (P : Subgroup (Alt 1 r)).map (alternatingGroup (X 1 r)).subtype := by
  let H := Subgroup.closure ({CFSGAlternatingSmallCrossSeed.p r,
    CFSGAlternatingSmallCrossSeed.q r hr, CFSGAlternatingSmallCrossSeed.b r hr} :
      Set (Equiv.Perm (X 1 r)))
  have heven : H ≤ alternatingGroup (X 1 r) := CFSGAlternatingSmallCrossSeed.seed_le_alternating r hr
  obtain ⟨P, hP⟩ := ((CFSGAlternatingSmallCrossSeed.seed_isPGroup r hr).comap_of_injective
    (alternatingGroup (X 1 r)).subtype
    (alternatingGroup (X 1 r)).subtype_injective).exists_le_sylow
  refine ⟨P, ?_⟩
  intro x hx
  exact ⟨⟨x, heven hx⟩, hP hx, rfl⟩

def smallReflectionElement (r : ℕ) : Alt 1 r :=
  ⟨CFSGAlternatingSmallCrossSeed.p r,
    extension_even (Cycle 1) r CFSGAlternatingSmallCrossSeed.baseReflection
      (Equiv.Perm.mem_alternatingGroup.mpr CFSGAlternatingSmallCrossSeed.baseReflection_even)⟩

theorem rotation_mem_rawJoin (r : ℕ) (P : Sylow 2 (Alt 1 r))
    (hp : CFSGAlternatingSmallCrossSeed.p r ∈
      (P : Subgroup (Alt 1 r)).map (alternatingGroup (X 1 r)).subtype) :
    g 1 r ∈ rawJoin 1 r P := by
  have hpP : smallReflectionElement r ∈ P := by
    obtain ⟨x, hx, he⟩ := hp
    have hxE : x = smallReflectionElement r := Subtype.ext he
    exact hxE ▸ hx
  have hg : rotationElement 1 r ∈ join 1 r P := by
    apply CFSGOddConjugateSubgroupExtraction.odd_element_mem_two_conjugates
      (P : Subgroup (Alt 1 r)) (smallReflectionElement r) (rotationElement 1 r) 2 hpP
    · apply Subtype.ext
      exact CFSGAlternatingSmallCrossSeed.p_square r
    · apply Subtype.ext
      simpa only [map_mul, map_inv] using congrArg (extensionHom (Cycle 1) r)
        CFSGAlternatingSmallCrossSeed.baseReflection_inverts
    · apply Subtype.ext
      change extensionHom (Cycle 1) r (rotation 1) ^ 5 = 1
      rw [← map_pow, rotation_odd_power 1, map_one]
  exact ⟨rotationElement 1 r, hg, rfl⟩

theorem adjacent_mem_rawJoin (r : ℕ) (hr : 2 ≤ r) (P : Sylow 2 (Alt 1 r))
    (hp : CFSGAlternatingSmallCrossSeed.p r ∈
      (P : Subgroup (Alt 1 r)).map (alternatingGroup (X 1 r)).subtype)
    (hb : CFSGAlternatingSmallCrossSeed.b r hr ∈
      (P : Subgroup (Alt 1 r)).map (alternatingGroup (X 1 r)).subtype) :
    extensionHom (Cycle 1) r (Equiv.swap (4 : Cycle 1) 0 * Equiv.swap 0 1) ∈ rawJoin 1 r P := by
  have hpK := rawSylow_le_rawJoin 1 r P hp
  have hbK := rawSylow_le_rawJoin 1 r P hb
  have ha : CFSGAlternatingSmallCrossWords.a r hr ∈ rawJoin 1 r P := by
    have h := (rawJoin 1 r P).mul_mem hpK hbK
    rwa [CFSGAlternatingSmallCrossWords.p_mul_b] at h
  have hg := rotation_mem_rawJoin r P hp
  have h := (rawJoin 1 r P).mul_mem ha
    ((rawJoin 1 r P).mul_mem ((rawJoin 1 r P).mul_mem hg ha) ((rawJoin 1 r P).inv_mem hg))
  rwa [CFSGAlternatingSmallCrossWords.adjacent_word] at h

theorem cycle_three_closure :
    Subgroup.closure ({rotation 1, Equiv.swap (4 : Cycle 1) 0 * Equiv.swap 0 1} :
      Set (Equiv.Perm (Cycle 1))) = alternatingGroup (Cycle 1) := by
  apply evenPairClosure_eq_alternating (by norm_num [Nat.card_eq_fintype_card, ZMod.card])
    (rotation 1) (Equiv.swap (0 : Cycle 1) 1) _ (Equiv.swap_inv _ _)
  · simpa only [show rotation 1 (0 : Cycle 1) = 1 by decide] using
      Equiv.Perm.closure_cycle_adjacent_swap (rotation_isCycle 1 (by decide))
        (rotation_support 1 (by decide)) (0 : Cycle 1)
  · exact Equiv.Perm.mem_alternatingGroup.mpr (rotation_even 1)
  · exact (rotation_isCycle 1 (by decide)).ne_one
  · exact Or.inl (cycle_adjacent_commutator (rotation 1) (4 : Cycle 1) 0 1 (by decide) (by decide))

theorem supported_alternating_mem (r : ℕ) (hr : 2 ≤ r) (P : Sylow 2 (Alt 1 r))
    (hp : CFSGAlternatingSmallCrossSeed.p r ∈
      (P : Subgroup (Alt 1 r)).map (alternatingGroup (X 1 r)).subtype)
    (hb : CFSGAlternatingSmallCrossSeed.b r hr ∈
      (P : Subgroup (Alt 1 r)).map (alternatingGroup (X 1 r)).subtype)
    (a : alternatingGroup (Cycle 1)) : extensionHom (Cycle 1) r a.val ∈ rawJoin 1 r P := by
  have hfull : alternatingGroup (Cycle 1) ≤
      (rawJoin 1 r P).comap (extensionHom (Cycle 1) r) := by
    rw [← cycle_three_closure]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact rotation_mem_rawJoin r P hp
    · exact adjacent_mem_rawJoin r hr P hp hb
  exact hfull a.property

theorem join_eq_top_of_pretransitive (r : ℕ) (hr : 2 ≤ r) (hr5 : r < 5)
    (P : Sylow 2 (Alt 1 r))
    (hp : CFSGAlternatingSmallCrossSeed.p r ∈
      (P : Subgroup (Alt 1 r)).map (alternatingGroup (X 1 r)).subtype)
    (hb : CFSGAlternatingSmallCrossSeed.b r hr ∈
      (P : Subgroup (Alt 1 r)).map (alternatingGroup (X 1 r)).subtype)
    [MulAction.IsPretransitive (rawJoin 1 r P) (X 1 r)] : join 1 r P = ⊤ := by
  have hfull : alternatingGroup (X 1 r) ≤ rawJoin 1 r P := by
    apply alternating_le_of_transitive_extension (Cycle 1) r (rawJoin 1 r P)
    · norm_num [ZMod.card]
    · simpa only [ZMod.card] using hr5
    · exact supported_alternating_mem r hr P hp hb
  apply (Subgroup.eq_top_iff' (join 1 r P)).mpr
  intro x
  obtain ⟨y, hy, he⟩ := hfull x.property
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

end SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossJoin
