import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationEndpointRecovery
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationPureShortOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationRootCoverage
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! A literal generating pair for the natural elementary type-B group
in every odd finite field and every rank at least three. The torus and
mixed Weyl word are retained through short-root extraction and coverage. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationFiniteFields
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationInitialElements
open CFSGOrthogonalBGenerationEndpointRecovery CFSGOrthogonalBGenerationPureShortOrbit
open CFSGOrthogonalBGenerationRootCoverage
variable (K : Type) [Field K] [Finite K]

theorem initial_pair_generate (h2 : (2 : K) ≠ 0) (s : ℕ)
    (hcard : 3 ≤ Nat.card K) (g : Kˣ) (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g) :
    Subgroup.closure ({initialTorus K h2 s g, initialMixedWeyl K s} :
      Set (elementaryRootGroup K (s + 3))) = ⊤ := by
  let R := Subgroup.closure ({initialTorus K h2 s g, initialMixedWeyl K s} :
    Set (elementaryRootGroup K (s + 3)))
  let H := R.map (elementaryRootGroup K (s + 3)).subtype
  have hT : (initialTorus K h2 s g).val ∈ H :=
    ⟨initialTorus K h2 s g, Subgroup.subset_closure (by simp), rfl⟩
  have hY : (initialMixedWeyl K s).val ∈ H :=
    ⟨initialMixedWeyl K s, Subgroup.subset_closure (by simp), rfl⟩
  obtain ⟨_, hW, hB⟩ := initial_pair_short_and_weyl K h2 hcard s g hg H hT hY
  have hShort := all_short_lines_of_weyl K (s + 2) H hW hB
  have hle := elementary_le_of_all_short K h2 s H hShort
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  exact (Subtype.ext he : y = x) ▸ hy

theorem elementary_exists_generating_pair (h2 : (2 : K) ≠ 0) (s : ℕ)
    (hcard : 3 ≤ Nat.card K) :
    ∃ x y : elementaryRootGroup K (s + 3),
      Subgroup.closure ({x, y} : Set (elementaryRootGroup K (s + 3))) = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨initialTorus K h2 s g, initialMixedWeyl K s,
    initial_pair_generate K h2 s hcard g hg⟩

theorem elementary_genRank_le_two (h2 : (2 : K) ≠ 0) (s : ℕ)
    (hcard : 3 ≤ Nat.card K) : MarkedC4.genRank (elementaryRootGroup K (s + 3)) ≤ 2 := by
  obtain ⟨x, y, hxy⟩ := elementary_exists_generating_pair K h2 s hcard
  have hc : Subgroup.closure (({x, y} : Finset (elementaryRootGroup K (s + 3))) :
      Set (elementaryRootGroup K (s + 3))) = ⊤ := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hxy
  exact (MarkedC4.genRank_le hc).trans Finset.card_le_two

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationFiniteFields
