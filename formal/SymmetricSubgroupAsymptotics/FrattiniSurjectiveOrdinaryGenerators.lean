import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.GroupTheory.Frattini

/-! Ordinary generating sets lift through an actual Frattini kernel
without adding generators. The source, target and surjection remain
literal; no splitting or normal-generator estimate is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FrattiniSurjectiveOrdinaryGenerators

variable {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]

theorem exists_generating_finset (f : G →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ frattini G) (S : Finset Q)
    (hS : Subgroup.closure (S : Set Q) = ⊤) :
    ∃ T : Finset G, Subgroup.closure (T : Set G) = ⊤ ∧ T.card ≤ S.card := by
  classical
  let lift : Q → G := fun q => Classical.choose (hf q)
  have hlift : ∀ q, f (lift q) = q := fun q => Classical.choose_spec (hf q)
  let T := S.image lift
  let C := Subgroup.closure (T : Set G)
  have hmap : C.map f = ⊤ := by
    apply top_unique
    rw [←hS]
    apply (Subgroup.closure_le _).mpr
    intro q hq
    refine ⟨lift q,Subgroup.subset_closure ?_,hlift q⟩
    exact Finset.mem_image.mpr ⟨q,hq,rfl⟩
  have hCker : C ⊔ f.ker = ⊤ := by
    have hh := congrArg (Subgroup.comap f) hmap
    simpa only [Subgroup.comap_map_eq,Subgroup.comap_top] using hh
  have hC : C = ⊤ := frattini_nongenerating (by
    apply top_unique
    rw [←hCker]
    exact sup_le_sup_left hker C)
  exact ⟨T,hC,Finset.card_image_le⟩

theorem genRank_le (f : G →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ frattini G) : MarkedC4.genRank G ≤ MarkedC4.genRank Q := by
  obtain ⟨S,hcard,hS⟩ := MarkedC4.genRank_spec (G := Q)
  obtain ⟨T,hT,hTcard⟩ := exists_generating_finset f hf hker S hS
  exact (MarkedC4.genRank_le hT).trans (hTcard.trans hcard.le)

end SymmetricSubgroupAsymptotics.FrattiniSurjectiveOrdinaryGenerators
