import SymmetricSubgroupAsymptotics.PermutationPairOrbitMarks
import SymmetricSubgroupAsymptotics.OrbitProfileProduct

/-!
# Actual pair-orbit marks in a full original profile

When precisely one original color has degree two, its actual occurrence
labels are in bijection with all two-point orbits. The resulting duplicate
mark equivalence preserves the unordered selected set. For the literal
product action, its equality test is equality of the two coordinate kernels
on the same original subgroup.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.OrbitProfilePairMarks

open PermutationPairOrbitMarks

variable {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}

def block (i : ι) (j : Fin (m i)) : Set (OrbitProfilePoints Ω m) :=
  Set.range (fun x : Ω i => (⟨i, j, x⟩ : OrbitProfilePoints Ω m))

theorem block_embedding_injective (i : ι) (j : Fin (m i)) :
    Function.Injective (fun x : Ω i => (⟨i, j, x⟩ : OrbitProfilePoints Ω m)) := by
  intro x y h
  have hp : (j, x) = (j, y) := by simpa using h
  exact congrArg Prod.snd hp

theorem block_card (i : ι) (j : Fin (m i)) :
    Nat.card (block (Ω := Ω) i j) = Nat.card (Ω i) :=
  Nat.card_range_of_injective (block_embedding_injective i j)

theorem block_index_injective [∀ i, Nonempty (Ω i)] (i : ι) :
    Function.Injective (block (Ω := Ω) (m := m) i) := by
  intro j l h
  let x : Ω i := Classical.choice inferInstance
  have hx : (⟨i, j, x⟩ : OrbitProfilePoints Ω m) ∈ block i l := by
    rw [← h]
    exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  have hp : (l, y) = (j, x) := by simpa using hy
  exact (congrArg Prod.fst hp).symm

variable [∀ i, Nonempty (Ω i)]
    {K : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))}
    (hK : OrbitProfileFull U 1 K)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (i₀ : ι) (hdegree : ∀ i, Nat.card (Ω i) = 2 ↔ i = i₀)

def pairOccurrence (j : Fin (m i₀)) : PairOrbit K :=
  ⟨block i₀ j, by
    constructor
    · let x : Ω i₀ := Classical.choice inferInstance
      refine ⟨(⟨i₀, j, x⟩ : OrbitProfilePoints Ω m), ?_⟩
      exact ((orbitProfileFullOn_iff U 1 K).mpr hK |>.orbit_eq_block htrans i₀ j x).symm
    · exact (block_card i₀ j).trans ((hdegree i₀).mpr rfl)⟩

theorem pairOccurrence_bijective : Function.Bijective (pairOccurrence hK htrans i₀ hdegree) := by
  constructor
  · intro j l h
    exact block_index_injective i₀ (congrArg Subtype.val h)
  · rintro ⟨s, ⟨⟨⟨i, j, x⟩, hs⟩, hc⟩⟩
    have hb : s = block (Ω := Ω) i j :=
      hs.trans ((orbitProfileFullOn_iff U 1 K).mpr hK |>.orbit_eq_block htrans i j x)
    have hi : i = i₀ := (hdegree i).mp (by rw [← block_card i j, ← hb]; exact hc)
    subst i
    exact ⟨j, Subtype.ext hb.symm⟩

/-- This equivalence remembers the literal original occurrence label. -/
def pairOrbitEquiv : Fin (m i₀) ≃ PairOrbit K :=
  Equiv.ofBijective (pairOccurrence hK htrans i₀ hdegree)
    (pairOccurrence_bijective hK htrans i₀ hdegree)

@[simp] theorem pairOrbitEquiv_val (j : Fin (m i₀)) :
    (pairOrbitEquiv hK htrans i₀ hdegree j).val = block i₀ j := rfl

include hK htrans hdegree in
theorem pairOrbit_card : Nat.card (PairOrbit K) = m i₀ := by
  rw [← Nat.card_congr (pairOrbitEquiv hK htrans i₀ hdegree), Nat.card_fin]

def OccurrenceDuplicate (s : Finset (Fin (m i₀))) : Prop :=
  s.card = 2 ∧ ∀ j ∈ s, ∀ l ∈ s, SameAction K (block i₀ j) (block i₀ l)

abbrev OccurrenceMark := {s : Finset (Fin (m i₀)) // OccurrenceDuplicate (K := K) i₀ s}

theorem occurrence_duplicate_iff (s : Finset (Fin (m i₀))) :
    OccurrenceDuplicate (K := K) i₀ s ↔
      IsDuplicate K (s.map (pairOrbitEquiv hK htrans i₀ hdegree).toEmbedding) := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨by simpa using hc, ?_⟩
    intro a ha b hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hb
    exact h j hj l hl
  · rintro ⟨hc, h⟩
    refine ⟨by simpa using hc, ?_⟩
    intro j hj l hl
    exact h _ (Finset.mem_map.mpr ⟨j, hj, rfl⟩)
      _ (Finset.mem_map.mpr ⟨l, hl, rfl⟩)

/-- No ordered-pair factor is introduced by identifying the physical marks. -/
def duplicateMarkEquiv : OccurrenceMark (K := K) i₀ ≃ DuplicateMark K :=
  (pairOrbitEquiv hK htrans i₀ hdegree).finsetCongr.subtypeEquiv
    (occurrence_duplicate_iff hK htrans i₀ hdegree)

theorem fixes_product_block (d : OrbitProfileProductGroup m U) (i : ι) (j : Fin (m i)) :
    Fixes (orbitProfileProductAction m U d) (block i j) ↔ d i j = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have hx := h ⟨i, j, x⟩ ⟨x, rfl⟩
    change (⟨i, j, (d i j : Equiv.Perm (Ω i)) x⟩ : OrbitProfilePoints Ω m) = ⟨i, j, x⟩ at hx
    have hp : (j, (d i j : Equiv.Perm (Ω i)) x) = (j, x) := by simpa using hx
    exact congrArg Prod.snd hp
  · intro hd x hx
    obtain ⟨y, rfl⟩ := hx
    change (⟨i, j, (d i j : Equiv.Perm (Ω i)) y⟩ : OrbitProfilePoints Ω m) = ⟨i, j, y⟩
    rw [hd]
    rfl

/-- The orbit mark compares original coordinate kernels before any collapse. -/
theorem sameAction_product_blocks (H : Subgroup (OrbitProfileProductGroup m U))
    (i : ι) (j l : Fin (m i)) :
    SameAction (H.map (orbitProfileProductAction m U)) (block i j) (block i l) ↔
      ∀ d ∈ H, d i j = 1 ↔ d i l = 1 := by
  constructor
  · intro h d hd
    exact (fixes_product_block d i j).symm.trans
      ((h _ (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)).trans (fixes_product_block d i l))
  · intro h g hg
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hg
    exact (fixes_product_block d i j).trans ((h d hd).trans (fixes_product_block d i l).symm)

end SymmetricSubgroupAsymptotics.OrbitProfilePairMarks
