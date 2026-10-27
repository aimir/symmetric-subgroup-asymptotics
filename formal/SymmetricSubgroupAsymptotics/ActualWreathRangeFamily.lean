import SymmetricSubgroupAsymptotics.ActualFullWreathFamily

/-! The literal range of an actual full-component embedding is a member
of the complete wreath family. No kernel or action data is forgotten. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathRangeFamily
open PermutationalWreathProduct ActualFullWreathFamily
variable {G D Q I : Type} [Group G] [Group D] [Group Q] [MulAction Q I]

def ofHom (rho : G →* PermutationalWreathProduct D Q I)
    (htop : Function.Surjective (rightHom.comp rho))
    (hfull : Compression.FullComponent rho) : Family D Q I := by
  refine ⟨rho.range,?_,?_⟩
  · apply top_unique
    intro q _
    obtain ⟨g,hg⟩ := htop q
    exact ⟨rho g,⟨g,rfl⟩,hg⟩
  · intro i d
    obtain ⟨g,hfix,hcoord⟩ := hfull i d
    exact ⟨⟨rho g,⟨g,rfl⟩⟩,hfix,hcoord⟩

theorem ofHom_subgroup (rho : G →* PermutationalWreathProduct D Q I)
    (htop : Function.Surjective (rightHom.comp rho))
    (hfull : Compression.FullComponent rho) : (ofHom rho htop hfull).val=rho.range := rfl
end SymmetricSubgroupAsymptotics.ActualWreathRangeFamily
