import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedModelEquivalence
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFoldedEquivalence
import SymmetricSubgroupAsymptotics.CFSGFFourE6NonAdjacentRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom

/-! A first actual positive ReeF4 fixed root chart. The orthogonal outer
nodes 0 and 3 give x0(a)*x3(alpha(a)), an injective additive parameter
subgroup of the literal original fixed group. This includes m=0 before
passing to any derived group or central quotient. No assertion about the
noncommuting middle orbit, whole positive group, or Tits quotient is made.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFixedRoot
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreQuadraticMatrix
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourFixedModelEquivalence CFSGFFourOriginalFoldedEquivalence
open CFSGFFourSerreMatrices CFSGFFourE6FixedGeneratedGroup CFSGFFourE6NonAdjacentRoots
open CFSGE6GeckRelativeSimpleHom CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckRelativeRootGenerated
open CFSGNormTwoCoordinateLeadingHom CFSGExceptionalCartanPositiveDefinite
local notation "A"=>CartanMatrix.F₄

private theorem source_root_zero (K:Type) [Field K] [Finite K] [CharP K 2] (i:Fin 4):
    modelRoot A K false i 0=1:=by
  apply (modelEquivFolded K).injective
  rw [modelEquivFolded_root,map_one]
  apply Subtype.ext
  exact canonicalRoot_zero realizationData K false i

private theorem source_root_add (K:Type) [Field K] [Finite K] [CharP K 2]
    (i:Fin 4) (a b:K):
    modelRoot A K false i (a+b)=modelRoot A K false i a*modelRoot A K false i b:=by
  apply (modelEquivFolded K).injective
  simp only [map_mul,modelEquivFolded_root]
  apply Subtype.ext
  exact (canonicalRoot_add realizationData K false i a b).symm

private theorem source_outer_commute (K:Type) [Field K] [Finite K] [CharP K 2] (a b:K):
    Commute (modelRoot A K false 0 a) (modelRoot A K false 3 b):=by
  apply (modelEquivFolded K).injective
  simp only [map_mul,modelEquivFolded_root]
  apply Subtype.ext
  change canonicalRoot realizationData K false 0 a*canonicalRoot realizationData K false 3 b=
    canonicalRoot realizationData K false 3 b*canonicalRoot realizationData K false 0 a
  have h:orbitParameter K false 0 a*orbitParameter K false 3 b=
      orbitParameter K false 3 b*orbitParameter K false 0 a:=
    (raw_nonadjacent_commute K 0 3 (by decide)
      (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)).eq
  simpa only [folded_root_eq_orbitParameter] using h

def outerWord (m:ℕ) (a:Field m):Model A (Field m):=
  modelRoot A (Field m) false 0 a*modelRoot A (Field m) false 3 (alpha m a)

theorem outerWord_fixed (m:ℕ) (a:Field m):reeAutomorphism m (outerWord m a)=outerWord m a:=by
  simp only [outerWord,map_mul,reeAutomorphism_root]
  change modelRoot A (Field m) false 3 (alpha m a)*
      modelRoot A (Field m) false 0 (beta m (alpha m a))=
    modelRoot A (Field m) false 0 a*modelRoot A (Field m) false 3 (alpha m a)
  rw [beta_alpha]
  exact (source_outer_commute (Field m) a (alpha m a)).eq.symm

def outerHom (m:ℕ):Multiplicative (Field m)→*Model A (Field m) where
  toFun a:=outerWord m a.toAdd
  map_one':=by
    change modelRoot A (Field m) false 0 0*modelRoot A (Field m) false 3 (alpha m 0)=1
    rw [map_zero,source_root_zero,source_root_zero,mul_one]
  map_mul' a b:=by
    change modelRoot A (Field m) false 0 (a.toAdd+b.toAdd)*
      modelRoot A (Field m) false 3 (alpha m (a.toAdd+b.toAdd))=_
    rw [map_add,source_root_add,source_root_add]
    exact (source_outer_commute (Field m) b.toAdd (alpha m a.toAdd)).mul_mul_mul_comm _ _

private def ambientRoot (m:ℕ) (i:Fin 6) (a:Field m):=
  positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (Field m) i a

private def ambientLeading (m:ℕ):=
  leadingHom CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (Field m)

private theorem ambientLeading_root (m:ℕ) (i:Fin 6) (a:Field m):
    ambientLeading m (ambientRoot m i a)=Multiplicative.ofAdd (Pi.single i a:Fin 6→Field m):=
  leadingHom_positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (Field m) i a

theorem outerWord_injective (m:ℕ):Function.Injective (outerWord m):=by
  intro a b he
  have hv:=congrArg (fun g:Model A (Field m)=>(modelEquivFolded (Field m) g).val) he
  simp only [outerWord,map_mul,modelEquivFolded_root,Subgroup.coe_mul] at hv
  change canonicalRoot realizationData (Field m) false 0 a*
      canonicalRoot realizationData (Field m) false 3 (alpha m a)=
    canonicalRoot realizationData (Field m) false 0 b*
      canonicalRoot realizationData (Field m) false 3 (alpha m b) at hv
  simp only [folded_root_eq_orbitParameter] at hv
  change canonicalRoot rawData (Field m) false 0 a*canonicalRoot rawData (Field m) false 5 a*
      canonicalRoot rawData (Field m) false 1 (alpha m a)=
    canonicalRoot rawData (Field m) false 0 b*canonicalRoot rawData (Field m) false 5 b*
      canonicalRoot rawData (Field m) false 1 (alpha m b) at hv
  have hx:ambientRoot m 0 a*ambientRoot m 5 a*ambientRoot m 1 (alpha m a)=
      ambientRoot m 0 b*ambientRoot m 5 b*ambientRoot m 1 (alpha m b):=Subtype.ext hv
  have hh:=congrArg (ambientLeading m) hx
  simp only [map_mul,ambientLeading_root] at hh
  have hc:=congrArg (fun z:Multiplicative (Fin 6→Field m)=>z.toAdd 0) hh
  simpa [Pi.single_apply] using hc

theorem outerHom_injective (m:ℕ):Function.Injective (outerHom m):=by
  intro a b he
  apply (Multiplicative.toAdd:Multiplicative (Field m)≃Field m).injective
  exact outerWord_injective m he

def fixedOuterHom (m:ℕ):Multiplicative (Field m)→* originalModelFixed m:=
  (outerHom m).codRestrict _ (fun a=>outerWord_fixed m a.toAdd)

theorem fixedOuterHom_injective (m:ℕ):Function.Injective (fixedOuterHom m):=by
  intro a b he
  exact outerHom_injective m (congrArg (fun g:originalModelFixed m=>g.val) he)

def originalFixedOuterHom (m:ℕ):Multiplicative (Field m)→*
    fixedSubgroup A (Field m) CFSG.Models.reverseNode (originalExponent m):=
  (originalFixedEquiv m).symm.toMonoidHom.comp (fixedOuterHom m)

theorem originalFixedOuterHom_val (m:ℕ) (a:Multiplicative (Field m)):
    (originalFixedOuterHom m a).val=(outerWord m a.toAdd).val:=rfl

theorem originalFixedOuterHom_injective (m:ℕ):Function.Injective (originalFixedOuterHom m):=
  (originalFixedEquiv m).symm.injective.comp (fixedOuterHom_injective m)

theorem originalFixedOuterHom_range_card (m:ℕ):
    Nat.card (originalFixedOuterHom m).range=2^(2*m+1):=by
  calc
    _=Nat.card (Multiplicative (Field m)):=
      (Nat.card_congr (MonoidHom.ofInjective (originalFixedOuterHom_injective m)).toEquiv).symm
    _=Nat.card (Field m):=Nat.card_congr Multiplicative.toAdd
    _=2^(2*m+1):=field_card m

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFixedRoot
