import SymmetricSubgroupAsymptotics.PrimeFrattiniGenerators
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Ordinary generators adapted to an actual product quotient. Each
generator projects into one literal product coordinate, or into the
identity. The finite p-group Frattini selection is made only after the
whole such family is shown to generate the original source. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PGroupProductAdaptedGenerators
open MarkedC4

variable (p : ℕ) [Fact p.Prime]
variable {G : Type*} [Group G] [Finite G]

theorem primeRank_le_genRank :
    Module.finrank (ZMod p) (PrimeCharacters p G) ≤ genRank G := by
  obtain ⟨S, hS, hgen⟩ := genRank_spec (G := G)
  let v : S → PrimeAbelianization p G := fun s =>
    primeAbelianizationMap p G (Additive.ofMul (s : G))
  have hspan : Submodule.span (ZMod p) (Set.range v) = ⊤ := by
    apply primeEvaluation_span_eq_top_of_generates p
      (fun s : S => (s : G))
    simpa only [Subtype.range_coe_subtype, Finset.setOf_mem] using hgen
  have h := finrank_le_of_span_eq_top hspan
  simpa only [Subspace.dual_finrank_eq, Fintype.card_coe, hS] using h

variable {I : Type*} [Fintype I]
    (P : I → Type*) [∀ i, Group (P i)]
    (π : G →* ∀ i, P i)

/-- The original quotient support of a single adapted generator. -/
def SingleSupport (g : G) : Prop :=
  π g = 1 ∨ ∃ (i : I) (x : P i), π g = Pi.mulSingle i x

/-- The adapted generating family is finite and has size at most the
ordinary generator number of the same original p-group. -/
theorem exists_adapted_generators (hG : IsPGroup p G)
    (hπ : Function.Surjective π) :
    ∃ S : Finset G, S.card ≤ genRank G ∧
      Subgroup.closure (S : Set G) = ⊤ ∧
      ∀ g ∈ S, SingleSupport P π g := by
  let A := {g : G // SingleSupport P π g}
  let z : A → G := Subtype.val
  let H := Subgroup.closure (Set.range z)
  have hker : π.ker ≤ H := by
    intro g hg
    exact Subgroup.subset_closure ⟨⟨g, Or.inl hg⟩, rfl⟩
  have hmap : H.map π = ⊤ := by
    apply top_unique
    intro y _
    apply Subgroup.pi_mem_of_mulSingle_mem
    intro i
    obtain ⟨g, hg⟩ := hπ (Pi.mulSingle i (y i))
    exact ⟨g, Subgroup.subset_closure ⟨⟨g, Or.inr ⟨i, y i, hg⟩⟩, rfl⟩, hg⟩
  have hgen : H = ⊤ := by
    have h := congrArg (Subgroup.comap π) hmap
    rw [Subgroup.comap_map_eq, Subgroup.comap_top, sup_eq_left.mpr hker] at h
    exact h
  obtain ⟨T, hT, hTgen⟩ := exists_generating_subtuple_le_primeRank p hG z hgen
    (MonoidHom.id G) Function.surjective_id
  let S : Finset G := T.image z
  refine ⟨S, Finset.card_image_le.trans (hT.trans (primeRank_le_genRank p)), ?_, ?_⟩
  · simpa only [S, Finset.coe_image, MonoidHom.coe_id, Set.image_id] using hTgen
  · intro g hg
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hg
    exact a.property

end SymmetricSubgroupAsymptotics.PGroupProductAdaptedGenerators
