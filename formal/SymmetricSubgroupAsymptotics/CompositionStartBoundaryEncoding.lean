import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Finite.Card
import Lean.Elab.Tactic.Omega

/-! Exact reconstruction of an actual composition from its nonterminal
start boundaries and its total mass. The zero start is retained when
the composition is nonempty, and the terminal mass is restored. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CompositionStartBoundaryEncoding

def startValues {s : ℕ} (c : Composition s) : Finset ℕ :=
  Finset.univ.image (fun i : Fin c.length => c.sizeUpTo i.val)

theorem boundaryValues_eq {s : ℕ} (c : Composition s) :
    c.boundaries.image (fun i : Fin (s + 1) => i.val) = startValues c ∪ {s} := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hx
    change a ∈ Finset.univ.map c.boundary.toEmbedding at ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp ha
    by_cases hj : j.val < c.length
    · apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_image.mpr ⟨⟨j.val,hj⟩,Finset.mem_univ _,hax⟩)
    · have he : j.val = c.length := by omega
      have hxs : x = s := by
        calc
          x = (c.boundary j).val := hax.symm
          _ = c.sizeUpTo j.val := rfl
          _ = c.sizeUpTo c.length := congrArg c.sizeUpTo he
          _ = s := c.sizeUpTo_length
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr hxs))
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨j,_,hjx⟩ := Finset.mem_image.mp hx
      apply Finset.mem_image.mpr
      refine ⟨c.boundary j.castSucc,?_,hjx⟩
      change c.boundary j.castSucc ∈ Finset.univ.map c.boundary.toEmbedding
      exact Finset.mem_map.mpr ⟨j.castSucc,Finset.mem_univ _,rfl⟩
    · have hxs : x = s := Finset.mem_singleton.mp hx
      subst x
      apply Finset.mem_image.mpr
      refine ⟨Fin.last s,?_,rfl⟩
      change Fin.last s ∈ Finset.univ.map c.boundary.toEmbedding
      exact Finset.mem_map.mpr ⟨Fin.last c.length,Finset.mem_univ _,c.boundary_last⟩

theorem composition_eq_of_startValues_eq {s : ℕ} (c d : Composition s)
    (he : startValues c = startValues d) : c = d := by
  have hnat : c.boundaries.image (fun i : Fin (s + 1) => i.val) =
      d.boundaries.image (fun i : Fin (s + 1) => i.val) := by
    rw [boundaryValues_eq,boundaryValues_eq,he]
  have hb : c.boundaries = d.boundaries :=
    Finset.image_injective
      (Fin.val_injective : Function.Injective (fun i : Fin (s + 1) => i.val)) hnat
  apply (compositionEquiv s).injective
  exact CompositionAsSet.ext hb

theorem sizeUpTo_lt_total {s : ℕ} (c : Composition s) (i : Fin c.length) :
    c.sizeUpTo i.val < s := by
  have h := c.boundary.strictMono (Fin.castSucc_lt_last i)
  change c.sizeUpTo i.val < c.sizeUpTo c.length at h
  simpa only [c.sizeUpTo_length] using h

theorem startValues_lt_total {s : ℕ} (c : Composition s) (x : ℕ)
    (hx : x ∈ startValues c) : x < s := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  exact sizeUpTo_lt_total c i

end SymmetricSubgroupAsymptotics.CompositionStartBoundaryEncoding
