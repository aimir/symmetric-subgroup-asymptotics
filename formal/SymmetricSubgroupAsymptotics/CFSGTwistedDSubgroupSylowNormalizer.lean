import SymmetricSubgroupAsymptotics.CFSGTwistedDTestNormalizer
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveSimpleUnipotent

/-! Any actual natural subgroup containing the retained tests has a
defining-characteristic Sylow with soluble normalizer. The initial
p-subgroup is the literal intersection with the standard D unipotent. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSubgroupSylowNormalizer
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDPositiveSimpleUnipotent CFSGTwistedDPartialFlagGeometry
open CFSGOrthogonalDGenerationForkTorus CFSGTwistedDTestNormalizer
variable (K : Type) [Field K] [Finite K] (s : ℕ)

theorem testRoot_mem_unipotent (i : Fin (s + 2) ⊕ Unit) :
    testRoot K s i ∈ unipotent K (s + 4) := by
  cases i with
  | inl i => exact positive_mem_unipotent K _ _ _
  | inr i =>
    exact (unipotent K (s + 4)).mul_mem
      (positive_mem_unipotent K _ _ _) (positive_mem_unipotent K _ _ _)

theorem exists_sylow_soluble_normalizer (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup (elementaryRootGroup K (s + 4))) (hT : ∀ i, testRoot K s i ∈ H) :
    ∃ Q : Sylow p H, IsSolvable (Subgroup.normalizer (Q : Set H)) := by
  let I := (unipotent K (s + 4)).subgroupOf H
  have hI : IsPGroup p I :=
    (unipotent_isPGroup K (s + 4) p).comap_of_injective H.subtype Subtype.val_injective
  obtain ⟨Q, hIQ⟩ := hI.exists_le_sylow
  let P : Subgroup (elementaryRootGroup K (s + 4)) := (Q : Subgroup H).map H.subtype
  have hP : IsPGroup p P := Q.isPGroup'.map H.subtype
  have hTP : ∀ i, testRoot K s i ∈ P := by
    intro i
    refine ⟨⟨testRoot K s i, hT i⟩, ?_, rfl⟩
    exact hIQ (testRoot_mem_unipotent K s i)
  let N := Subgroup.normalizer (Q : Set H)
  let M := Subgroup.normalizer (P : Set (elementaryRootGroup K (s + 4)))
  letI : IsSolvable M := normalizer_soluble K s p P hP hTP
  let f : N →* M :=
    { toFun := fun g => ⟨g.val.val,
        (Q : Subgroup H).le_normalizer_map H.subtype ⟨g.val, g.property, rfl⟩⟩
      map_one' := Subtype.ext rfl
      map_mul' _ _ := Subtype.ext rfl }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : M => z.val) he
  exact ⟨Q, solvable_of_solvable_injective (f := f) hf⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDSubgroupSylowNormalizer
