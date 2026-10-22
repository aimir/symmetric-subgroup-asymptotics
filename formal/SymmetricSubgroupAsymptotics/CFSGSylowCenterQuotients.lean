import SymmetricSubgroupAsymptotics.CFSGSylowCenterRecognition

/-! Onto homomorphisms send actual Sylow-centre elements to actual
Sylow-centre elements. The same map is used on the subgroup and its
central element; no injectivity or lifting assertion is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSylowCenterRecognition
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem map_mem_sylowCenterElements (p : ℕ) [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f) {x : G}
    (hx : x ∈ sylowCenterElements (G := G) p) :
    f x ∈ sylowCenterElements (G := H) p := by
  obtain ⟨P, z, hz, rfl⟩ := hx
  let Q : Sylow p H := P.mapSurjective (f := f) hf
  let h : P →* Q := f.subgroupMap (P : Subgroup G)
  refine ⟨Q, h z, ?_, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨t, rfl⟩ := f.subgroupMap_surjective (P : Subgroup G) y
  simpa only [map_mul] using congrArg h (Subgroup.mem_center_iff.mp hz t)

end SymmetricSubgroupAsymptotics.CFSGSylowCenterRecognition
