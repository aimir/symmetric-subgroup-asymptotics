import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fin.Basic

/-! Generator positions lift additively through an actual exact sequence
of modules. The proof uses literal spans, actual kernel equality and
chosen preimages; no group-generation analogue is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ModuleGeneratorExactSequence

variable {A U V W : Type} [Ring A]
    [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W]

/-- An m-position kernel module and n-position quotient module generate
the same original middle module in m+n positions. -/
theorem span_tuple_of_exact (i : U →ₗ[A] V) (q : V →ₗ[A] W)
    (hexact : LinearMap.range i = LinearMap.ker q) (hq : Function.Surjective q)
    {m n : ℕ} (u : Fin m → U) (hu : Submodule.span A (Set.range u) = ⊤)
    (w : Fin n → W) (hw : Submodule.span A (Set.range w) = ⊤) :
    ∃ v : Fin (m+n) → V, Submodule.span A (Set.range v) = ⊤ := by
  let lift : Fin n → V := fun j => Classical.choose (hq (w j))
  have hlift (j : Fin n) : q (lift j) = w j := Classical.choose_spec (hq (w j))
  let seed : Fin (m+n) → V := Fin.addCases (fun j => i (u j)) lift
  let P : Submodule A V := Submodule.span A (Set.range seed)
  have hleft (j : Fin m) : i (u j) ∈ P :=
    Submodule.subset_span ⟨Fin.castAdd n j,by simp [seed]⟩
  have hright (j : Fin n) : lift j ∈ P :=
    Submodule.subset_span ⟨Fin.natAdd m j,by simp [seed]⟩
  have hi : LinearMap.range i ≤ P := by
    have hs : Submodule.span A (Set.range u) ≤ P.comap i := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact hleft j
    rw [hu] at hs
    rintro _ ⟨x,rfl⟩
    exact hs (Submodule.mem_top : x ∈ (⊤ : Submodule A U))
  have hk : LinearMap.ker q ≤ P := by rw [←hexact]; exact hi
  have hmap : Submodule.span A (Set.range w) ≤ P.map q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨lift j,hright j,hlift j⟩
  refine ⟨seed,top_unique ?_⟩
  intro v _
  have hm : q v ∈ P.map q := hmap (by rw [hw]; trivial)
  obtain ⟨p,hp,he⟩ := hm
  have hd : v-p ∈ LinearMap.ker q := by
    change q (v-p) = 0
    rw [map_sub,he,sub_self]
  have hmem := P.add_mem (hk hd) hp
  simpa only [sub_add_cancel] using hmem

end SymmetricSubgroupAsymptotics.ModuleGeneratorExactSequence
