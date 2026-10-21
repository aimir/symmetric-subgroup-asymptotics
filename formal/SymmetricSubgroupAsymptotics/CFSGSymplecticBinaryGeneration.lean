import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRootCoverage
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! A uniform literal generating pair for the elementary symplectic
group over the two-element field, in every rank at least three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryGeneration
open Matrix CFSGSymplecticSerreMatrices CFSGSymplecticBinaryPairElements
open CFSGSymplecticBinaryRootCoverage
variable {K : Type} [Field K] [CharP K 2]

theorem binary_pair_generate (hcard : Nat.card K=2) (s : ℕ) :
    Subgroup.closure ({binaryFirst K s,binarySecond K s} : Set (elementaryRootGroup K (s+3)))=⊤ := by
  let R := Subgroup.closure ({binaryFirst K s,binarySecond K s} : Set (elementaryRootGroup K (s+3)))
  let H := R.map (elementaryRootGroup K (s+3)).subtype
  have hX : (binaryFirst K s).val∈H :=
    ⟨binaryFirst K s,Subgroup.subset_closure (Set.mem_insert _ _),rfl⟩
  have hW : (binarySecond K s).val∈H :=
    ⟨binarySecond K s,Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)),rfl⟩
  have hle : elementaryRootGroup K (s+3)≤H := elementary_le_of_pair hcard s H hX hW
  apply top_unique
  intro x _
  have hx : x.val∈H := hle x.property
  obtain ⟨y,hy,he⟩ := hx
  have heq : y=x := Subtype.ext he
  exact heq ▸ hy

theorem elementary_exists_generating_pair (hcard : Nat.card K=2) (s : ℕ) :
    ∃x y : elementaryRootGroup K (s+3),Subgroup.closure ({x,y} : Set (elementaryRootGroup K (s+3)))=⊤ :=
  ⟨binaryFirst K s,binarySecond K s,binary_pair_generate hcard s⟩

theorem elementary_genRank_le_two [Finite K] (hcard : Nat.card K=2) (s : ℕ) :
    MarkedC4.genRank (elementaryRootGroup K (s+3))≤2 := by
  have hc : Subgroup.closure
      (({binaryFirst K s,binarySecond K s} : Finset (elementaryRootGroup K (s+3))) :
        Set (elementaryRootGroup K (s+3)))=⊤ := by
    simpa only [Finset.coe_insert,Finset.coe_singleton] using binary_pair_generate hcard s
  exact (MarkedC4.genRank_le hc).trans Finset.card_le_two

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryGeneration
