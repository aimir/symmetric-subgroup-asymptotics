import SymmetricSubgroupAsymptotics.Row62OriginalQuartetFrame
import SymmetricSubgroupAsymptotics.Row62CyclicFourKernelModel
import SymmetricSubgroupAsymptotics.SchreierKernelImageContainment
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row62OriginalKernelCertificate
open Row62OriginalQuartetFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
private def code (p : Equiv.Perm (Fin 3)) : Nat :=
  (p 0).val+3*(p 1).val+9*(p 2).val
private def sectionWord (p : Equiv.Perm (Fin 3)) : FiniteGeneratorWord (Fin 3) :=
  if code p=21 then .one else
  if code p=15 then (.mul (.mul .one (.generator 2)) (.generator 1)) else
  if code p=19 then (.mul .one (.generator 2)) else
  if code p=7 then (.mul .one (.generator 1)) else
  if code p=11 then (.mul (.mul .one (.generator 1)) (.generator 1)) else
  if code p=5 then (.mul (.mul (.mul .one (.generator 2)) (.generator 1)) (.generator 1)) else
  .one

def liftSection (p : Equiv.Perm (Fin 3)) : Row62Top := (sectionWord p).eval original
private theorem word_top (w : FiniteGeneratorWord (Fin 3)) :
    frame.top (w.eval original)=w.eval tops := by
  rw [FiniteGeneratorWord.map_eval]
  congr 1
  funext i
  exact generator_top i
 theorem section_top (p : Equiv.Perm (Fin 3)) : frame.top (liftSection p)=p := by
  rw [liftSection,word_top]
  revert p
  decide +kernel
 theorem section_one : liftSection 1=1 := by rfl
private def coordinates (p : Equiv.Perm (Fin 3)) (i : Fin 3) :
    CyclicFourAugmentationTranslations.Model := Multiplicative.ofAdd <|
  if code p=21 ∧ i=0 then ![3,0] else
  if code p=21 ∧ i=1 then ![0,0] else
  if code p=21 ∧ i=2 then ![0,0] else
  if code p=15 ∧ i=0 then ![3,1] else
  if code p=15 ∧ i=1 then ![0,0] else
  if code p=15 ∧ i=2 then ![0,0] else
  if code p=19 ∧ i=0 then ![0,3] else
  if code p=19 ∧ i=1 then ![0,0] else
  if code p=19 ∧ i=2 then ![0,0] else
  if code p=7 ∧ i=0 then ![1,3] else
  if code p=7 ∧ i=1 then ![0,0] else
  if code p=7 ∧ i=2 then ![0,0] else
  if code p=11 ∧ i=0 then ![0,1] else
  if code p=11 ∧ i=1 then ![0,0] else
  if code p=11 ∧ i=2 then ![0,0] else
  if code p=5 ∧ i=0 then ![1,0] else
  if code p=5 ∧ i=1 then ![0,0] else
  if code p=5 ∧ i=2 then ![0,0] else
  0
private theorem point_identity : ∀ (p : Equiv.Perm (Fin 3)) (i : Fin 3),
    (liftSection p : Equiv.Perm (Fin 12)) * row62Generators i *
      (liftSection (p*tops i) : Equiv.Perm (Fin 12))⁻¹ =
        Row62CyclicFourKernelModel.action (coordinates p i) := by
  decide +kernel
 theorem kernel_mem (k : frame.top.ker) :
    (k.val : Equiv.Perm (Fin 12)) ∈ Row62CyclicFourKernelModel.action.range := by
  apply schreier_kernel_image_mem original (closureGenerators_full row62Generators)
    frame.top liftSection section_top section_one Row62Top.subtype
    Row62CyclicFourKernelModel.action.range ?_ k
  rintro ⟨p,i⟩
  refine ⟨coordinates p i,?_⟩
  change Row62CyclicFourKernelModel.action (coordinates p i)=
    (liftSection p : Equiv.Perm (Fin 12)) * row62Generators i *
      (liftSection (p*frame.top (original i)) : Equiv.Perm (Fin 12))⁻¹
  rw [generator_top]
  exact (point_identity p i).symm
end SymmetricSubgroupAsymptotics.Row62OriginalKernelCertificate
