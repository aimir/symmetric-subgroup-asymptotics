import SymmetricSubgroupAsymptotics.CFSGRankOneBruhatClosure
import SymmetricSubgroupAsymptotics.CFSGSuzukiBruhatCell
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentWeylGeneration
import SymmetricSubgroupAsymptotics.CFSGSuzukiFixedLine

/-! The two Bruhat cells of the literal pinned Suzuki matrix model.
The nonzero big-cell matrix entry also computes the normalizer of its
actual unipotent group inside the actual generated model. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSG.Models.SuzukiConstruction CFSGSuzukiTorus CFSGSuzukiBruhat

theorem model_two_cells (m : ℕ) (g : Ambient m) (hg : g ∈ subgroup m) :
    g ∈ borelEnvelope m ∨ ∃ b ∈ borelEnvelope m,
      ∃ u ∈ unipotentSubgroup m, g = b * weylElement m * u := by
  apply CFSGRankOneBruhat.closure_le_two_cells
    (borelEnvelope m) (unipotentSubgroup m) (normalizedTorusHom m).range
    (weylElement m) (unipotentSubgroup_le_borelEnvelope m)
    (fun t ht => by
      obtain ⟨c,rfl⟩ := ht
      exact normalizedTorus_mem_borelEnvelope m c)
    (le_of_eq (borelEnvelope_eq_unipotent_sup_torus m))
    (normalizedTorus_normalizes_unipotent m)
    (weyl_normalizes_torus m) (weylElement_square m)
    (weyl_unipotent_cell m) g
  simpa only [closure_borel_weyl] using hg

theorem big_cell_entry_ne_zero (m : ℕ) (b : Ambient m)
    (hb : b ∈ borelEnvelope m) (u : Ambient m)
    (hu : u ∈ unipotentSubgroup m) :
    ((b * weylElement m * u : Ambient m) : Mat m) 0 3 ≠ 0 := by
  obtain ⟨a,d,c,rfl⟩ := borelEnvelope_factor m b hb
  obtain ⟨x,y,rfl⟩ := hu
  rw [big_cell_entry_zero_three]
  exact Units.ne_zero c

/-- The intersection with the actual model is essential: scalar matrices
in the ambient general linear group also normalize U. -/
theorem normalizer_inter_model_le_borel (m : ℕ) :
    (Subgroup.normalizer (unipotentSubgroup m : Set (Ambient m)) ⊓ subgroup m) ≤
      borelEnvelope m := by
  intro g hg
  rcases model_two_cells m g hg.2 with hb | ⟨b,hb,u,hu,he⟩
  · exact hb
  · have hz := (normalizer_last_column m g hg.1).1
    rw [he] at hz
    exact False.elim (big_cell_entry_ne_zero m b hb u hu hz)

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
