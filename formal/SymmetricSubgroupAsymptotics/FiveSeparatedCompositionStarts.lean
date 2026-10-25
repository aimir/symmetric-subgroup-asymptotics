import SymmetricSubgroupAsymptotics.CompositionStartBoundaryEncoding
import SymmetricSubgroupAsymptotics.FiveSeparatedCutCardinality

/-! A composition whose actual parts are at least five has separated
nonterminal starts. Its exact total restores the terminal boundary, so
embedding these starts in ANY larger finite interval loses no data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiveSeparatedCompositionStarts
open CompositionStartBoundaryEncoding FiveSeparatedCutCardinality

def startCuts {s : ℕ} (n : ℕ) (c : Composition s) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val ∈ startValues c)

theorem mem_startCuts {s n : ℕ} (c : Composition s) (i : Fin n) :
    i ∈ startCuts n c ↔ i.val ∈ startValues c := by
  simp only [startCuts,Finset.mem_filter,Finset.mem_univ,true_and]

theorem startCuts_image_val {s : ℕ} (n : ℕ) (c : Composition s) (hbound : s ≤ n) :
    (startCuts n c).image (fun i : Fin n => i.val) = startValues c := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨i,hi,hix⟩ := Finset.mem_image.mp hx
    exact hix ▸ (mem_startCuts c i).mp hi
  · intro hx
    have hlt : x < n := (startValues_lt_total c x hx).trans_le hbound
    exact Finset.mem_image.mpr ⟨⟨x,hlt⟩,(mem_startCuts c ⟨x,hlt⟩).mpr hx,rfl⟩

theorem startValues_gap {s : ℕ} (c : Composition s)
    (hlarge : ∀ a ∈ c.blocks, 5 ≤ a) (x y : ℕ)
    (hx : x ∈ startValues c) (hy : y ∈ startValues c) (hxy : x < y) :
    x + 5 ≤ y := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
  have hij : i.val < j.val := by
    by_contra h
    have hji : j.val ≤ i.val := by omega
    have hm := c.monotone_sizeUpTo hji
    omega
  have hstep := c.sizeUpTo_succ' i
  have hpart := hlarge (c.blocksFun i) (c.blocksFun_mem_blocks i)
  have hm : c.sizeUpTo (i.val + 1) ≤ c.sizeUpTo j.val :=
    c.monotone_sizeUpTo (Nat.succ_le_of_lt hij)
  omega

def separatedStarts {s : ℕ} (n : ℕ) (c : Composition s)
    (hlarge : ∀ a ∈ c.blocks, 5 ≤ a) : SeparatedCuts n :=
  ⟨startCuts n c,by
    intro i hi j hj hij
    exact startValues_gap c hlarge i.val j.val
      ((mem_startCuts c i).mp hi) ((mem_startCuts c j).mp hj) hij⟩

theorem composition_eq_of_startCuts_eq {s : ℕ} (n : ℕ) (c d : Composition s)
    (hbound : s ≤ n) (he : startCuts n c = startCuts n d) : c = d := by
  have h := congrArg (fun t : Finset (Fin n) => t.image (fun i => i.val)) he
  dsimp only at h
  rw [startCuts_image_val n c hbound,startCuts_image_val n d hbound] at h
  exact composition_eq_of_startValues_eq c d h

end SymmetricSubgroupAsymptotics.FiveSeparatedCompositionStarts
