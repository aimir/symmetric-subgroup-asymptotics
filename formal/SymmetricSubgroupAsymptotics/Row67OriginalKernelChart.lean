import SymmetricSubgroupAsymptotics.Row67OriginalKernelCertificate
import SymmetricSubgroupAsymptotics.BinarySymmetricThreeAugmentation
import SymmetricSubgroupAsymptotics.OriginalKernelModuleChartFromSection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row67OriginalKernelChart
open Row67OriginalQuartetFrame
open BinaryPlaneAugmentationTranslations (Model)
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
private def unitWord (i j : Fin 2) : FiniteGeneratorWord (Fin 4) :=
  let t := if j=0 then .mul (.generator 0) (.generator 1) else .generator 1
  if i=0 then t else .mul (.mul (.mul (.generator 2) t) (.inv (.generator 2))) t
private def word (v : Model) : FiniteGeneratorWord (Fin 4) :=
  let u := fun i j => if v.toAdd i j=0 then FiniteGeneratorWord.one else unitWord i j
  .mul (.mul (u 0 0) (u 0 1)) (.mul (u 1 0) (u 1 1))
private theorem word_top : ∀ v : Model,frame.top ((word v).eval original)=1 := by
  intro v
  rw [FiniteGeneratorWord.map_eval]
  have he : (fun i => frame.top (original i))=tops := funext generator_top
  rw [he]
  revert v
  decide +kernel
private theorem word_points : ∀ v : Model,
    (((word v).eval original : Row67Top) : Equiv.Perm (Fin 12))=Row67BinaryPlaneKernelModel.action v := by
  decide +kernel
 def kernelMap : Model →* frame.top.ker where
  toFun v := ⟨(word v).eval original,word_top v⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change (((word 1).eval original : Row67Top) : Equiv.Perm (Fin 12))=1
    rw [word_points,map_one]
  map_mul' v w := by
    apply Subtype.ext
    apply Subtype.ext
    change (((word (v*w)).eval original : Row67Top) : Equiv.Perm (Fin 12))=
      (((word v).eval original : Row67Top) : Equiv.Perm (Fin 12))*(((word w).eval original : Row67Top) : Equiv.Perm (Fin 12))
    rw [word_points,word_points,word_points,map_mul]
 theorem kernelMap_bijective : Function.Bijective kernelMap := by
  constructor
  · intro v w h
    apply Row67BinaryPlaneKernelModel.action_injective
    have hp := congrArg (fun z : frame.top.ker => (z.val : Equiv.Perm (Fin 12))) h
    change (((word v).eval original : Row67Top) : Equiv.Perm (Fin 12))=
      (((word w).eval original : Row67Top) : Equiv.Perm (Fin 12)) at hp
    rw [word_points,word_points] at hp
    exact hp
  · intro k
    obtain ⟨v,hv⟩ := Row67OriginalKernelCertificate.kernel_mem k
    refine ⟨v,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (word_points v).trans hv
 def kernelEquiv : Model ≃* frame.top.ker := MulEquiv.ofBijective kernelMap kernelMap_bijective
abbrev R : Rep (ZMod 2) (Equiv.Perm (Fin 3)) := Rep.of BinarySymmetricThreeAugmentation.rho
private theorem section_conjugate : ∀ (p : Equiv.Perm (Fin 3)) (v : R),
    (kernelEquiv (Multiplicative.ofAdd (R.ρ p v)) : Row67Top)=
      Row67OriginalKernelCertificate.liftSection p*
      (kernelEquiv (Multiplicative.ofAdd v) : Row67Top)*
      (Row67OriginalKernelCertificate.liftSection p)⁻¹ := by
  intro p v
  apply Subtype.ext
  change (((word (Multiplicative.ofAdd (R.ρ p v))).eval original : Row67Top) : Equiv.Perm (Fin 12))=_
  rw [word_points]
  change Row67BinaryPlaneKernelModel.action (Multiplicative.ofAdd (R.ρ p v))=
    (Row67OriginalKernelCertificate.liftSection p : Equiv.Perm (Fin 12))*
      (((word (Multiplicative.ofAdd v)).eval original : Row67Top) : Equiv.Perm (Fin 12))*
      (Row67OriginalKernelCertificate.liftSection p : Equiv.Perm (Fin 12))⁻¹
  rw [word_points]
  revert p v
  decide +kernel
 def chart : OriginalKernelModuleChart frame.top R :=
  OriginalKernelModuleChart.ofSection frame.top R kernelEquiv
    Row67OriginalKernelCertificate.liftSection Row67OriginalKernelCertificate.section_top
    section_conjugate
end SymmetricSubgroupAsymptotics.Row67OriginalKernelChart
