import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFoldedEquivalence
import SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeWords
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddlePairedCollecting
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleFactorInjective

/-! Literal original F4 middle B2 words and their already-checked E6
values. The original Model correspondence is faithful, without ordinary
F4 simplicity, so the raw collecting identity returns to the same source.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWords
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreQuadraticMatrix
open CFSGFFourSerreMatrices CFSGFFourOriginalFoldedEquivalence CFSGFFourE6RelativeWords
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6RelativeWeylOrbits
open CFSGTwistedE6GeckRelativeRootGenerated CFSGE6GeckSignedSimpleParameters
open CFSGE6GeckMiddleAThreeCollecting CFSGE6GeckMiddlePairedCollecting
open CFSGE6GeckMiddleFactorInjective CFSGSerreQuadraticWeylWord
variable (K:Type) [Field K] [Finite K] [CharP K 2]
local notation "A"=>CartanMatrix.F₄

def rawHom:Model A K→*(Matrix Index Index K)ˣ:=
  (canonicalElementaryGroup realizationData K).subtype.comp (modelEquivFolded K).toMonoidHom

theorem rawHom_injective:Function.Injective (rawHom K):=
  Subtype.val_injective.comp (modelEquivFolded K).injective

theorem rawHom_root (neg:Bool) (i:Fin 4) (t:K):
    rawHom K (modelRoot A K neg i t)=canonicalRoot realizationData K neg i t:=by
  change (modelEquivFolded K (modelRoot A K neg i t)).val=_
  rw [modelEquivFolded_root]
  rfl

def weyl (i:Fin 4):Model A K:=
  modelRoot A K false i 1*modelRoot A K true i (-1)*modelRoot A K false i 1

theorem rawHom_weyl (i:Fin 4):rawHom K (weyl K i)=canonicalWeyl realizationData K i:=by
  simp only [weyl,map_mul,rawHom_root,canonicalWeyl]

def middleLong (t:K):Model A K:=
  weyl K 1*modelRoot A K false 2 t*(weyl K 1)⁻¹

def middleShort (t:K):Model A K:=
  weyl K 2*modelRoot A K false 1 t*(weyl K 2)⁻¹

theorem rawHom_middleLong (t:K):rawHom K (middleLong K t)=highestMiddle K t:=by
  have hw:canonicalWeyl realizationData K 1=
      canonicalWeyl rawData K 2*canonicalWeyl rawData K 4:=by
    have h := foldedWeyl_eq_orbitWord K 1
    change canonicalWeyl realizationData K 1 = canonicalWord rawData K [2,4] at h
    simpa only [canonicalWord,mul_one] using h
  have hr:canonicalRoot realizationData K false 2 t=canonicalRoot rawData K false 3 t:=by
    rw [CFSGFFourE6FixedGeneratedGroup.folded_root_eq_orbitParameter]
    rfl
  simp only [middleLong,map_mul,map_inv,rawHom_weyl,rawHom_root,hw,hr,highestMiddle]

theorem rawHom_middleShort (t:K):
    rawHom K (middleShort K t)=middlePair K (RingEquiv.refl K) t:=by
  have hw:canonicalWeyl realizationData K 2=canonicalWeyl rawData K 3:=by
    have h := foldedWeyl_eq_orbitWord K 2
    change canonicalWeyl realizationData K 2 = canonicalWord rawData K [3] at h
    simpa only [canonicalWord,mul_one] using h
  have hr:canonicalRoot realizationData K false 1 t=
      rawPairedHom K (RingEquiv.refl K) false 1 (Multiplicative.ofAdd t):=by
    rw [CFSGFFourE6FixedGeneratedGroup.folded_root_eq_orbitParameter]
    rfl
  simp only [middleShort,map_mul,map_inv,rawHom_weyl,rawHom_root,hw,hr,middlePair]

theorem middle_commutator (a b:K):
    ⁅modelRoot A K false 1 a,modelRoot A K false 2 b⁆=
      middleLong K (a^2*b)*middleShort K (a*b):=by
  apply rawHom_injective K
  rw [map_commutatorElement,map_mul,rawHom_root,rawHom_root,rawHom_middleLong,rawHom_middleShort]
  have hr (i:Fin 4) (t:K):canonicalRoot realizationData K false i t=orbitParameter K false i t:=
    CFSGFFourE6FixedGeneratedGroup.folded_root_eq_orbitParameter K false i t
  rw [hr,hr]
  have h:=middle_paired_commutator K (RingEquiv.refl K) a b rfl
  change ⁅rawPairedHom K (RingEquiv.refl K) false 1 (Multiplicative.ofAdd a),
    rawSingletonHom K false 1 (Multiplicative.ofAdd b)⁆=_
  simpa only [RingEquiv.refl_apply,CharTwo.neg_eq,pow_two,middlePair] using h

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWords
