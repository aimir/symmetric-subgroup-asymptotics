import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionProductLift
import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionProductGeometry
import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionFamilies
import SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveTransvectionRecognition

/-! Concrete projective root families. A rank-one projective product
lifts to the exact original product and forces a common centre or axis.
The uniform-family theorem retains the original representative vectors
and forms; no abstract point geometry or model correspondence is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveRootFamilies
open Matrix Module LinearMap Submodule CFSGTypeAProjectivePointRoots
open CFSGTypeATransvectionProductLift CFSGTypeATransvectionProductGeometry
open CFSGTypeATransvectionFamilies CFSGTypeAProjectiveTransvectionRecognition
variable {F : Type*} [Field F] {n : ℕ}

theorem projective_product_common_centre_or_axis (hn : 3≤n)
    {f g h : Dual F (Fin n→F)} {v w u : Fin n→F}
    (hfv : f v=0) (hgw : g w=0) (hhu : h u=0)
    (hf : f≠0) (hg : g≠0) (hv : v≠0) (hw : w≠0)
    (he : projection (transvectionSL hfv)*projection (transvectionSL hgw)=
      projection (transvectionSL hhu)) :
    (F ∙ v)=(F ∙ w) ∨ LinearMap.ker f=LinearMap.ker g := by
  have hSL := transvection_product_eq_of_projective_eq
    (by simpa only [Fintype.card_fin] using hn) hfv hgw hhu he
  have hlin : (LinearMap.transvection f v).comp (LinearMap.transvection g w)=
      LinearMap.transvection h u := by
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun A : Matrix.SpecialLinearGroup (Fin n) F => A.toLin' x) hSL
    dsimp only at hh
    rw [map_mul] at hh
    change (transvectionSL hfv).toLin' ((transvectionSL hgw).toLin' x)=
      (transvectionSL hhu).toLin' x at hh
    simpa only [transvectionSL_apply,LinearMap.comp_apply,LinearMap.transvection.apply] using hh
  exact product_transvection_common_centre_or_axis hf hg hv hw hlin

theorem common_centre_or_axis_of_projective_products {ι : Type*} (hn : 3≤n)
    (f : ι→Dual F (Fin n→F)) (v : ι→Fin n→F) (hfv : ∀i,f i (v i)=0)
    (hf : ∀i,f i≠0) (hv : ∀i,v i≠0)
    (hprod : ∀i j,IsProjectiveTransvection
      (projection (transvectionSL (hfv i))*projection (transvectionSL (hfv j)))) :
    (∀i j,(F ∙ v i)=(F ∙ v j)) ∨ (∀i j,LinearMap.ker (f i)=LinearMap.ker (f j)) := by
  apply uniform_coordinate_of_pairwise (fun i => F ∙ v i) (fun i => LinearMap.ker (f i))
  intro i j
  obtain ⟨h,u,hhu,he⟩ := hprod i j
  exact projective_product_common_centre_or_axis hn (hfv i) (hfv j) hhu
    (hf i) (hf j) (hv i) (hv j) he

end SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveRootFamilies
