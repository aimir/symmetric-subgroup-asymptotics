import SymmetricSubgroupAsymptotics.Row59OriginalCutSpaceCoordinates
import SymmetricSubgroupAsymptotics.TetrahedralCutSpaceSchreierKernelChart
import SymmetricSubgroupAsymptotics.TetrahedralCutSpaceOriginalQuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeOrbitNaturalBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row59CutSpaceOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open Row59OriginalCutSpaceFrame
open Row59OriginalCutSpaceCoordinates
open AlternatingEdgeOriginalProjectorHeads (Top)
open TetrahedralCutSpaceEdgeEmbedding (embedding)
local instance : Inhabited (FiniteGeneratorWord (Fin 4)) := ⟨.one⟩

def permutationCode (p : Equiv.Perm (Fin 4)) : Fin 256 :=
  ⟨(p 0).val+4*(p 1).val+16*(p 2).val+64*(p 3).val,by have := (p 0).isLt; have := (p 1).isLt; have := (p 2).isLt; have := (p 3).isLt; omega⟩
def sectionWord (p : Equiv.Perm (Fin 4)) : FiniteGeneratorWord (Fin 4) :=
  (#[.one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, (.mul (.generator 3) (.mul (.generator 2) (.mul (.inv (.generator 3)) .one))), .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, (.mul (.generator 2) (.mul (.generator 3) (.mul (.generator 2) .one))), .one, .one, .one, .one, .one, .one, .one, .one, (.mul (.generator 2) (.mul (.inv (.generator 3)) .one)), .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, (.mul (.generator 2) .one), .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, (.mul (.generator 2) (.mul (.inv (.generator 3)) (.mul (.generator 2) .one))), .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, (.mul (.generator 3) .one), .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, (.mul (.generator 3) (.mul (.generator 2) .one)), .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, (.mul (.inv (.generator 3)) .one), .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, (.mul (.inv (.generator 3)) (.mul (.generator 2) (.mul (.generator 3) .one))), .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, (.mul (.inv (.generator 3)) (.mul (.generator 2) .one)), .one, .one, .one, .one, .one, .one, .one, .one, (.mul (.generator 2) (.mul (.generator 3) .one)), .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one] : Array (FiniteGeneratorWord (Fin 4)))[(permutationCode p).val]!
def liftSection (p : Top) : row59Interface.top := (sectionWord p.val).eval original
private theorem section_top (p : Top) : top (liftSection p)=p := by
  have hm := (sectionWord p.val).map_eval top original
  have hc : (fun i => top (original i))=codes := funext top_generator
  rw [hc] at hm
  apply Subtype.ext
  change (top ((sectionWord p.val).eval original)).val=p.val
  rw [hm]
  have hf : ∀ q : Equiv.Perm (Fin 4),Equiv.Perm.sign q=1 → ((sectionWord q).eval codes).val=q := by decide +kernel
  exact hf p.val p.property
private theorem section_one : liftSection 1=1 := rfl
private theorem section_val (p : Top) :
    (liftSection p : Equiv.Perm (Fin 12))=(sectionWord p.val).eval row59Generators := by
  have hm := (sectionWord p.val).map_eval row59Interface.top.subtype original
  have hc : (fun i => row59Interface.top.subtype (original i))=row59Generators := by funext i; rfl
  rw [hc] at hm
  exact hm

def coordinates (p : Equiv.Perm (Fin 4)) (i : Fin 4) : TetrahedralCutSpaceCoinvariantHead.Vector :=
  (((#[#[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![1,1,0], ![0,1,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,1,1], ![0,0,1], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![1,0,1], ![1,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![1,1,0], ![0,0,1], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![1,0,1], ![1,1,1], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,1,1], ![0,1,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,1,1], ![1,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![1,0,1], ![0,0,1], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![1,1,0], ![1,1,1], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![1,0,1], ![0,1,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,1,1], ![1,1,1], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![1,1,0], ![1,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]], #[![0,0,0], ![0,0,0], ![0,0,0], ![0,0,0]]] : Array (Array TetrahedralCutSpaceCoinvariantHead.Vector))[(permutationCode p).val]!)[i.val]!)
private theorem schreier_val (p : Top) (i : Fin 4) :
    ((schreierKernelGenerators original top liftSection section_top (p,i)).val : Equiv.Perm (Fin 12))=
      (sectionWord p.val).eval row59Generators*row59Generators i*
        ((sectionWord (p*codes i).val).eval row59Generators)⁻¹ := by
  change ((liftSection p*original i*(liftSection (p*top (original i)))⁻¹ : row59Interface.top) : Equiv.Perm (Fin 12))=_
  rw [top_generator]
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,section_val]
  rfl
private theorem relation_coordinates (p : Top) (i : Fin 4) :
    inclusion (originalKernelChart.equiv.symm
      (schreierKernelGenerators original top liftSection section_top (p,i))).toAdd=
        embedding (coordinates p.val i) := by
  funext x
  rw [coordinate_apply,schreier_val]
  have hf : ∀ (q : Equiv.Perm (Fin 4)),Equiv.Perm.sign q=1 → ∀ (j : Fin 4) (y : Fin 6),
    (points.symm (((sectionWord q).eval row59Generators*row59Generators j*
      ((sectionWord (q*(codes j).val)).eval row59Generators)⁻¹) (points (y,0)))).2=
        embedding (coordinates q j) y := by decide +kernel
  exact hf p.val p.property i x
private theorem relation_mem (z : Top × Fin 4) :
    inclusion (originalKernelChart.equiv.symm
      (schreierKernelGenerators original top liftSection section_top z)).toAdd∈embedding.range :=
  ⟨coordinates z.1.val z.2,(relation_coordinates z.1 z.2).symm⟩

def basisWord : Fin 3 → FiniteGeneratorWord (Fin 4) :=
  ![(.mul (.generator 1) .one),(.mul (.generator 3) (.mul (.generator 1) (.mul (.inv (.generator 3)) .one))),(.mul (.generator 3) (.mul (.generator 3) (.mul (.generator 1) (.mul (.inv (.generator 3)) (.mul (.inv (.generator 3)) .one)))))]
private theorem basis_top (i : Fin 3) : top ((basisWord i).eval original)=1 := by
  have hm := (basisWord i).map_eval top original
  have hc : (fun j => top (original j))=codes := funext top_generator
  rw [hc] at hm
  have hf : ∀ k : Fin 3,(basisWord k).eval codes=1 := by decide +kernel
  exact hm.trans (hf i)
def basisKernel (i : Fin 3) : top.ker := ⟨(basisWord i).eval original,basis_top i⟩
private theorem basis_coordinates (i : Fin 3) :
    inclusion (originalKernelChart.equiv.symm (basisKernel i)).toAdd=embedding (Pi.single i 1) := by
  funext x
  rw [coordinate_apply]
  have hm := (basisWord i).map_eval row59Interface.top.subtype original
  have hc : (fun j => row59Interface.top.subtype (original j))=row59Generators := by funext j; rfl
  rw [hc] at hm
  change (((basisWord i).eval original : row59Interface.top) : Equiv.Perm (Fin 12)) =
    (basisWord i).eval row59Generators at hm
  change (points.symm ((((basisWord i).eval original : row59Interface.top) : Equiv.Perm (Fin 12)) (points (x,0)))).2=_
  rw [hm]
  clear hm hc
  revert i x
  decide +kernel

def cutChart : OriginalKernelModuleChart top TetrahedralCutSpaceOriginalHeads.R :=
  TetrahedralCutSpaceSchreierKernelChart.chart originalKernelChart inclusion inclusion_injective
    original (closureGenerators_full row59Generators) liftSection section_top section_one relation_mem
    (fun i => ⟨basisKernel i,basis_coordinates i⟩)
theorem quotientSocle (N : Subgroup row59Interface.top) [N.Normal] :
    SocleNormalGeneratorBound (row59Interface.top ⧸ N) 1 :=
  TetrahedralCutSpaceOriginalQuotientSocles.quotientSocle top
    (AlternatingEdgePairFrameKernel.top_surjective frame topEquiv) cutChart N

def jointData : DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row59Interface 1 3 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact quotientSocle N.1)
  natural := PrimitiveAffineDegreeTwoTwelveThreeOrbitNaturalBounds.row59NaturalThree
def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row59Interface :=
  .ofExact jointData (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row59CutSpaceOriginalJointData
