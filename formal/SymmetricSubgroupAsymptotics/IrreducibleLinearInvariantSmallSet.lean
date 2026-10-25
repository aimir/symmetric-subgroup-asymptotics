import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Group.End

/-! An irreducible linear action of dimension greater than one has no
nonempty invariant set of nonzero vectors with cardinal at most its
dimension. Its span would be the whole space; that small spanning family
is independent, so its invariant sum is nonzero and gives an invariant
line. The proof works over any field and uses no finite-group census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.IrreducibleLinearInvariantSmallSet

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

theorem sum_fixed_of_invariant_finset
    (ρ : G →* (V ≃ₗ[K] V)) (s : Finset V)
    (hstable : ∀ (g : G) (v : V), ρ g v ∈ s ↔ v ∈ s) (g : G) :
    ρ g (∑ v : s, (v : V)) = ∑ v : s, (v : V) := by
  let e : s ≃ s := (ρ g).toEquiv.subtypeEquiv (fun v => (hstable g v).symm)
  rw [map_sum]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem finrank_lt_card_of_invariant_nonzero_finset [FiniteDimensional K V]
    (ρ : G →* (V ≃ₗ[K] V))
    (hirr : ∀ W : Submodule K V,
      (∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hdim : 1 < Module.finrank K V) (s : Finset V) (hs : s.Nonempty)
    (hzero : 0 ∉ s) (hstable : ∀ (g : G) (v : V), ρ g v ∈ s ↔ v ∈ s) :
    Module.finrank K V < s.card := by
  by_contra hlarge
  have hsmall : s.card ≤ Module.finrank K V := by omega
  let W := Submodule.span K (s : Set V)
  have hWstable (g : G) (v : V) (hv : v ∈ W) : ρ g v ∈ W := by
    refine Submodule.span_induction (fun x hx => ?_) ?_
      (fun x y _ _ hx hy => ?_) (fun a x _ hx => ?_) hv
    · exact Submodule.subset_span ((hstable g x).mpr hx)
    · simpa only [map_zero] using W.zero_mem
    · simpa only [map_add] using W.add_mem hx hy
    · simpa only [map_smul] using W.smul_mem a hx
  have hWbot : W ≠ ⊥ := by
    intro he
    obtain ⟨v, hv⟩ := hs
    have hmem : v ∈ W := Submodule.subset_span hv
    rw [he] at hmem
    have hvzero : v = 0 := (Submodule.mem_bot K).mp hmem
    exact hzero (hvzero ▸ hv)
  have hWtop : W = ⊤ := (hirr W hWstable).resolve_left hWbot
  have hrange : Set.range (fun v : s => (v : V)) = (s : Set V) := by
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      exact u.property
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩
  have hi : LinearIndependent K (fun v : s => (v : V)) := by
    apply linearIndependent_of_top_le_span_of_card_le_finrank
    · rw [hrange]
      exact hWtop.ge
    · simpa only [Fintype.card_coe] using hsmall
  let z : V := ∑ v : s, (v : V)
  have hz : z ≠ 0 := by
    intro he
    have hcoeff := (Fintype.linearIndependent_iff.mp hi) (fun _ : s => (1 : K))
      (by simpa only [one_smul] using he)
    obtain ⟨v, hv⟩ := hs
    exact one_ne_zero (hcoeff ⟨v, hv⟩)
  have hfixed (g : G) : ρ g z = z := sum_fixed_of_invariant_finset ρ s hstable g
  let Z : Submodule K V := K ∙ z
  have hZstable (g : G) (v : V) (hv : v ∈ Z) : ρ g v ∈ Z := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, hfixed g]
    exact Z.smul_mem a (Submodule.mem_span_singleton_self z)
  have hZbot : Z ≠ ⊥ := by
    intro he
    have hmem : z ∈ Z := Submodule.mem_span_singleton_self z
    rw [he] at hmem
    exact hz ((Submodule.mem_bot K).mp hmem)
  have hZtop : Z = ⊤ := (hirr Z hZstable).resolve_left hZbot
  have hZdim : Module.finrank K Z = 1 := finrank_span_singleton hz
  rw [hZtop, finrank_top K V] at hZdim
  omega

end SymmetricSubgroupAsymptotics.IrreducibleLinearInvariantSmallSet
