import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient

/-! The entire full-component family, including arbitrary base
intersections, and its literal images under local chief quotients. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualFullWreathFamily
open PermutationalWreathProduct

variable (R Q I : Type) [Group R] [Group Q] [MulAction Q I]

abbrev Family := {L : Subgroup (PermutationalWreathProduct R Q I) //
  L.map rightHom=⊤ ∧ Compression.FullComponent L.subtype}

variable {R Q I}

theorem top_surjective (L : Family R Q I) :
    Function.Surjective (rightHom.comp L.val.subtype) := by
  intro q
  have hq : q∈L.val.map rightHom := by rw [L.property.1]; exact Subgroup.mem_top q
  obtain ⟨g,hg,hq⟩ := hq
  exact ⟨⟨g,hg⟩,hq⟩

def localImage {R' : Type} [Group R'] (phi : R →* R')
    (hphi : Function.Surjective phi) (L : Family R Q I) : Family R' Q I := by
  refine ⟨L.val.map (mapBase phi),?_,?_⟩
  · apply top_unique
    intro q _
    obtain ⟨g,hg⟩ := top_surjective L q
    exact ⟨mapBase phi g.val,⟨g.val,g.property,rfl⟩,hg⟩
  · intro i r'
    obtain ⟨r,rfl⟩ := hphi r'
    obtain ⟨g,hfix,hcoord⟩ := L.property.2 i r
    refine ⟨⟨mapBase phi g.val,⟨g.val,g.property,rfl⟩⟩,hfix,?_⟩
    exact congrArg phi hcoord

theorem localImage_subgroup {R' : Type} [Group R'] (phi : R →* R')
    (hphi : Function.Surjective phi) (L : Family R Q I) :
    (localImage phi hphi L).val=L.val.map (mapBase phi) := rfl

end SymmetricSubgroupAsymptotics.ActualFullWreathFamily
