import SymmetricSubgroupAsymptotics.CFSGAlternatingCrossSeed
import SymmetricSubgroupAsymptotics.CFSGOddConjugateSubgroupExtraction

/-! The same actual Sylow and its rotation conjugate contain the full
supported alternating group on the cycle. The argument retains the literal
original sum carrier and actual subgroup inclusions throughout. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingCrossJoin
open CFSGAlternatingCyclicReflection CFSGAlternatingCyclicDoubleSwap
open CFSGAlternatingSumSupport CFSGAlternatingCrossSeed

abbrev Alt (k r : ℕ) := alternatingGroup (X k r)

def rotationElement (k r : ℕ) : Alt k r :=
  ⟨g k r, extension_even (Cycle k) r (rotation k)
    (Equiv.Perm.mem_alternatingGroup.mpr (rotation_even k))⟩

def reflectionElement (k r : ℕ) : Alt k r :=
  ⟨p k r, extension_even (Cycle k) r (reflection k)
    (Equiv.Perm.mem_alternatingGroup.mpr (reflection_even k))⟩

def join (k r : ℕ) (P : Sylow 2 (Alt k r)) : Subgroup (Alt k r) :=
  Subgroup.closure ((P : Set (Alt k r)) ∪
    (P : Subgroup (Alt k r)).map (MulAut.conj (rotationElement k r)).toMonoidHom)

def rawJoin (k r : ℕ) (P : Sylow 2 (Alt k r)) : Subgroup (Equiv.Perm (X k r)) :=
  (join k r P).map (alternatingGroup (X k r)).subtype

theorem rawSylow_le_rawJoin (k r : ℕ) (P : Sylow 2 (Alt k r)) :
    (P : Subgroup (Alt k r)).map (alternatingGroup (X k r)).subtype ≤ rawJoin k r P := by
  apply Subgroup.map_mono
  intro x hx
  exact Subgroup.subset_closure (Or.inl hx)

theorem rotation_mem_rawJoin (k r : ℕ) (P : Sylow 2 (Alt k r))
    (hp : p k r ∈ (P : Subgroup (Alt k r)).map (alternatingGroup (X k r)).subtype) :
    g k r ∈ rawJoin k r P := by
  have hpP : reflectionElement k r ∈ P := by
    obtain ⟨x, hx, he⟩ := hp
    have hxE : x = reflectionElement k r := Subtype.ext he
    exact hxE ▸ hx
  have hg : rotationElement k r ∈ join k r P := by
    apply CFSGOddConjugateSubgroupExtraction.odd_element_mem_two_conjugates
      (P : Subgroup (Alt k r)) (reflectionElement k r) (rotationElement k r) (2 * k) hpP
    · apply Subtype.ext
      change extensionHom (Cycle k) r (reflection k) ^ 2 = 1
      rw [← map_pow, reflection_square, map_one]
    · apply Subtype.ext
      simpa only [map_mul, map_inv] using
        congrArg (extensionHom (Cycle k) r) (reflection_inverts k)
    · apply Subtype.ext
      change extensionHom (Cycle k) r (rotation k) ^ (2 * (2 * k) + 1) = 1
      rw [show 2 * (2 * k) + 1 = 4 * k + 1 by omega, ← map_pow,
        rotation_odd_power, map_one]
  exact ⟨rotationElement k r, hg, rfl⟩

theorem supported_alternating_mem_rawJoin (k r : ℕ) (hk : 2 ≤ k)
    (P : Sylow 2 (Alt k r))
    (hp : p k r ∈ (P : Subgroup (Alt k r)).map (alternatingGroup (X k r)).subtype)
    (ha : a k r ∈ (P : Subgroup (Alt k r)).map (alternatingGroup (X k r)).subtype)
    (b : alternatingGroup (Cycle k)) :
    extensionHom (Cycle k) r b.val ∈ rawJoin k r P := by
  let L := (rawJoin k r P).comap (extensionHom (Cycle k) r)
  have hL : alternatingGroup (Cycle k) ≤ L := by
    apply alternating_le_of_rotation_doubleSwap k hk L
    · exact rotation_mem_rawJoin k r P hp
    · exact rawSylow_le_rawJoin k r P ha
  exact hL b.property

theorem join_eq_top_of_pretransitive (k r : ℕ) (hk : 2 ≤ k) (hr : r < 4 * k + 1)
    (P : Sylow 2 (Alt k r))
    (hp : p k r ∈ (P : Subgroup (Alt k r)).map (alternatingGroup (X k r)).subtype)
    (ha : a k r ∈ (P : Subgroup (Alt k r)).map (alternatingGroup (X k r)).subtype)
    [MulAction.IsPretransitive (rawJoin k r P) (X k r)] : join k r P = ⊤ := by
  have hfull : alternatingGroup (X k r) ≤ rawJoin k r P := by
    apply alternating_le_of_transitive_extension (Cycle k) r (rawJoin k r P)
    · rw [ZMod.card]; omega
    · simpa only [ZMod.card] using hr
    · exact supported_alternating_mem_rawJoin k r hk P hp ha
  apply (Subgroup.eq_top_iff' (join k r P)).mpr
  intro x
  obtain ⟨y, hy, he⟩ := hfull x.property
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

end SymmetricSubgroupAsymptotics.CFSGAlternatingCrossJoin
