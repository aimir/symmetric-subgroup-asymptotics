import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionRootParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionDiagramLabels
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceActionCovariance

/-! The constructed original section chart has the literal field action
on a diagram-fixed root. Its fixed parameters are EXACTLY the defining
subfield parameters. Matrix conjugator fixity and chart injectivity prove
this, without source faithfulness or a fixed-class lifting assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionParameterTwist
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckSectionDiagramLabels
open CFSGTwistedE6GeckRelativeWordTwist CFSGTwistedE6GeckOriginalRootSections
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckSourceActionCovariance CFSGTwistedE6GeckDiagramCovariance
open CFSGSerreQuadraticMatrix CFSGSerreOrdinaryTwists CFSGTwistedE6WeylChamber

def firstMatrixRoot (q : CFSG.PrimePower) (k : PositiveRoot) (t : q.Extension 2) : MatrixGroup (q.Extension 2) :=
  matrixTransport q k*canonicalElementaryRoot rawData (q.Extension 2) true (sectionNode k) t*
    (matrixTransport q k)⁻¹

def secondMatrixRoot (q : CFSG.PrimePower) (k : PositiveRoot) (t : q.Extension 2) : MatrixGroup (q.Extension 2) :=
  matrixTransport q k*canonicalElementaryRoot rawData (q.Extension 2) true
    (CFSG.Models.e6Twist (sectionNode k)) t*(matrixTransport q k)⁻¹

theorem firstMatrixRoot_val (q : CFSG.PrimePower) (k : PositiveRoot) (t : q.Extension 2) :
    (firstMatrixRoot q k t).val=(sectionParameter (q.Extension 2) k t).val :=
  conjugated_seed_parameter q k t

theorem firstMatrixRoot_twist (q : CFSG.PrimePower) (k : PositiveRoot)
    (sigma : q.Extension 2≃+*q.Extension 2) (t : q.Extension 2) :
    matrixGroupTwist (q.Extension 2) sigma (firstMatrixRoot q k t)=secondMatrixRoot q k (sigma t) := by
  simp only [firstMatrixRoot,secondMatrixRoot,map_mul,map_inv,matrixTransport_fixed,
    matrixGroupTwist_root,CFSGSerreDiagram.e6Permutation_apply]

theorem singleton_parameter_twist (q : CFSG.PrimePower) (k : PositiveRoot)
    (hk : diagramRoot k.val=k.val) (sigma : q.Extension 2≃+*q.Extension 2) (t : q.Extension 2) :
    unitTwist (q.Extension 2) sigma (sectionParameter (q.Extension 2) k t).val=
      (sectionParameter (q.Extension 2) k (sigma t)).val := by
  have hj := (section_seed_fixed_iff k).mpr hk
  have he : matrixGroupTwist (q.Extension 2) sigma (firstMatrixRoot q k t)=
      firstMatrixRoot q k (sigma t) := by
    rw [firstMatrixRoot_twist]
    simp only [secondMatrixRoot,firstMatrixRoot,hj]
  have hv := congrArg Subtype.val he
  change unitTwist (q.Extension 2) sigma (firstMatrixRoot q k t).val=(firstMatrixRoot q k (sigma t)).val at hv
  rw [firstMatrixRoot_val,firstMatrixRoot_val] at hv
  exact hv

theorem singleton_parameter_fixed_iff (q : CFSG.PrimePower) (k : PositiveRoot)
    (hk : diagramRoot k.val=k.val) (t : q.Extension 2) :
    unitTwist (q.Extension 2) (definingFieldAutomorphism q 2)
      (sectionParameter (q.Extension 2) k t).val=(sectionParameter (q.Extension 2) k t).val ↔
        t^q.order=t := by
  rw [singleton_parameter_twist q k hk]
  constructor
  · intro he
    have hx : sectionParameterMulEquiv (q.Extension 2) k
        (Multiplicative.ofAdd (definingFieldAutomorphism q 2 t))=
      sectionParameterMulEquiv (q.Extension 2) k (Multiplicative.ofAdd t) := Subtype.ext he
    have ht := congrArg Multiplicative.toAdd ((sectionParameterMulEquiv (q.Extension 2) k).injective hx)
    change definingFieldAutomorphism q 2 t=t at ht
    simpa only [definingFieldAutomorphism_apply] using ht
  · intro ht
    have hs : definingFieldAutomorphism q 2 t=t := by
      simpa only [definingFieldAutomorphism_apply] using ht
    rw [hs]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionParameterTwist
