import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationEndpointRecovery
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationInitialExtraction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPureRootCoverage
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! The literal nonbinary D generating pair in every rank at least
four. Extraction, both endpoint geometries and original simple-root
coverage are assembled without a rank-parity or classical-group premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationFiniteFields
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationInitialRootMatrices
open CFSGOrthogonalDGenerationInitialExtraction CFSGOrthogonalDGenerationEndpointRecovery
open CFSGOrthogonalDGenerationRootLineTransport CFSGOrthogonalDGenerationSignedRootConjugation
open CFSGOrthogonalDGenerationPureRootCoverage
variable (K : Type) [Field K] [Finite K]

theorem initial_pair_generate (s : ℕ) (hcard : 3 ≤ Nat.card K) (g : Kˣ)
    (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g) :
    Subgroup.closure ({initialTorus K s g, initialMixedWeyl K s} :
      Set (elementaryRootGroup K (s + 4))) = ⊤ := by
  let R := Subgroup.closure ({initialTorus K s g, initialMixedWeyl K s} :
    Set (elementaryRootGroup K (s + 4)))
  have hT : initialTorus K s g ∈ R := Subgroup.subset_closure (by simp)
  have hY : initialMixedWeyl K s ∈ R := Subgroup.subset_closure (by simp)
  obtain ⟨hB, hy⟩ := star_line_and_cleaned_word K s hcard g hg R hT hY
  let H := R.map (elementaryRootGroup K (s + 4)).subtype
  have hBline : HasRootLine H (rootArray K
      (Sum.inl (second s)) (Sum.inr (CFSGOrthogonalDGenerationForkTorus.last (s + 2)))) := by
    intro a
    refine ⟨(initialStarRoot K s false a).val, ⟨initialStarRoot K s false a, hB a, rfl⟩, ?_⟩
    exact initialStarRoot_coe K s false a
  have hy' : (initialShortRoot K s 1).val * (coxeterWeyl K (s + 3)).val ∈ H :=
    ⟨initialShortRoot K s 1 * coxeterWeyl K (s + 3), hy, rfl⟩
  obtain ⟨hA, hW⟩ := recover_short_and_weyl K s hcard g hg H hy' hBline
  have hle := elementary_le_of_root_lines K s H hW hA hBline
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  exact (Subtype.ext he : y = x) ▸ hy

theorem elementary_exists_generating_pair (s : ℕ) (hcard : 3 ≤ Nat.card K) :
    ∃ x y : elementaryRootGroup K (s + 4),
      Subgroup.closure ({x, y} : Set (elementaryRootGroup K (s + 4))) = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨initialTorus K s g, initialMixedWeyl K s, initial_pair_generate K s hcard g hg⟩

theorem elementary_genRank_le_two (s : ℕ) (hcard : 3 ≤ Nat.card K) :
    MarkedC4.genRank (elementaryRootGroup K (s + 4)) ≤ 2 := by
  obtain ⟨x, y, hxy⟩ := elementary_exists_generating_pair K s hcard
  have hc : Subgroup.closure (({x, y} : Finset (elementaryRootGroup K (s + 4))) :
      Set (elementaryRootGroup K (s + 4))) = ⊤ := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hxy
  exact (MarkedC4.genRank_le hc).trans Finset.card_le_two

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationFiniteFields
