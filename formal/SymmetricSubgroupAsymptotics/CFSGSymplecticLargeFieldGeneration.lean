import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialRootCoverage

/-! Two explicit actual elementary C generators over every finite field
of order at least four, in every rank at least two. The proof recovers
all original simple roots inside their literal generated subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem initial_pair_generate (K : Type) [Field K] [Finite K]
    (hcard : 4 ≤ Nat.card K) (r : ℕ) (hr : 0 < r) (g : Kˣ)
    (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g) :
    Subgroup.closure ({initialTorus K r g, initialMixedWeyl K r} :
      Set (elementaryRootGroup K (r + 1))) = ⊤ := by
  let H := Subgroup.closure ({initialTorus K r g, initialMixedWeyl K r} :
    Set (elementaryRootGroup K (r + 1)))
  have hx : initialTorus K r g ∈ H := Subgroup.subset_closure (by simp)
  have hy : initialMixedWeyl K r ∈ H := Subgroup.subset_closure (by simp)
  obtain ⟨hA, hW⟩ := initial_pair_short_and_weyl K hcard r hr g hg H hx hy
  have hB := all_secondLong_parameters_of_initial_pair K hcard r hr g hg H hx hy
  exact elementary_eq_top_of_initial_root_lines K r hr H hW hA hB

theorem elementary_large_field_exists_generating_pair (K : Type) [Field K] [Finite K]
    (hcard : 4 ≤ Nat.card K) (s : ℕ) :
    ∃ x y : elementaryRootGroup K (s + 2),
      Subgroup.closure ({x, y} : Set (elementaryRootGroup K (s + 2))) = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨initialTorus K (s + 1) g, initialMixedWeyl K (s + 1),
    initial_pair_generate K hcard (s + 1) (by omega) g hg⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
