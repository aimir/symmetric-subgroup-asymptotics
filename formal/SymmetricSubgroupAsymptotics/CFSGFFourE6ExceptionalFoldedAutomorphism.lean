import SymmetricSubgroupAsymptotics.CFSGFFourE6NormActionFaithful
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientActionRange

/-! An actual exceptional automorphism of the literal folded matrix group
over every finite field of characteristic two. The checked norm26 action
identifies the group with its image; the transported quotient26 action has
exactly that image. No ordinary F4 simplicity or original F4 correspondence
is used or asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6ExceptionalFoldedAutomorphism
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6NormActionFaithful
open CFSGFFourE6NormQuotientActionRange
variable (K:Type) [Field K] [Finite K] [CharP K 2]

def exceptionalEnd :
    canonicalElementaryGroup realizationData K→*canonicalElementaryGroup realizationData K :=
  (MonoidHom.ofInjective (normAction_injective K)).symm.toMonoidHom.comp
    ((MulEquiv.subgroupCongr (action_ranges_eq K)).toMonoidHom.comp
      (quotientOnNorm K).rangeRestrict)

theorem exceptionalEnd_intertwines (g:canonicalElementaryGroup realizationData K) :
    normAction K (exceptionalEnd K g)=quotientOnNorm K g := by
  change normAction K ((MonoidHom.ofInjective (normAction_injective K)).symm
    (MulEquiv.subgroupCongr (action_ranges_eq K) ((quotientOnNorm K).rangeRestrict g)))=_
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem exceptionalEnd_surjective : Function.Surjective (exceptionalEnd K) :=
  (MonoidHom.ofInjective (normAction_injective K)).symm.surjective.comp
    ((MulEquiv.subgroupCongr (action_ranges_eq K)).surjective.comp
      (quotientOnNorm K).rangeRestrict_surjective)

theorem exceptionalEnd_injective : Function.Injective (exceptionalEnd K) := by
  letI : Fintype K:=Fintype.ofFinite K
  exact Finite.injective_iff_surjective.mpr (exceptionalEnd_surjective K)

def exceptionalFoldedEquiv : MulAut (canonicalElementaryGroup realizationData K) :=
  MulEquiv.ofBijective (exceptionalEnd K)
    ⟨exceptionalEnd_injective K,exceptionalEnd_surjective K⟩

theorem exceptionalFoldedEquiv_root (neg:Bool) (i:Fin 4) (t:K) :
    exceptionalFoldedEquiv K (foldedRoot K neg i t)=
      foldedRoot K neg (reversedNode i) (exceptionalParameter i t) := by
  apply normAction_injective K
  change normAction K (exceptionalEnd K (foldedRoot K neg i t))=_
  rw [exceptionalEnd_intertwines,quotientOnNorm_root]

theorem exceptionalFoldedEquiv_twice_root (neg:Bool) (i:Fin 4) (t:K) :
    exceptionalFoldedEquiv K (exceptionalFoldedEquiv K (foldedRoot K neg i t))=
      foldedRoot K neg i (t^2) := by
  rw [exceptionalFoldedEquiv_root,exceptionalFoldedEquiv_root]
  fin_cases i <;> rfl

end SymmetricSubgroupAsymptotics.CFSGFFourE6ExceptionalFoldedAutomorphism
