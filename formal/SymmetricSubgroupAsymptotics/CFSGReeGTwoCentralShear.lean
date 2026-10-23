import SymmetricSubgroupAsymptotics.CFSGReeGTwoMiddleShearRigidity
import SymmetricSubgroupAsymptotics.CFSGCentralCocyclePGroup

/-! An actual U3 automorphism fixing a and c has a central difference.
The checked centralDifferenceHom makes that difference a genuine hom;
its additive first-coordinate factor is the actual d-shear. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoCentralShear
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCoordinates CFSGReeGTwoPositiveFirstQuotient
open CFSGReeGTwoPositiveCentre CFSGReeGTwoPositiveDerivedKernel
open CFSGReeGTwoPositiveAutomorphismLayers CFSGSurjectiveGroupHomFactor
open scoped commutatorElement

theorem central_difference_eq (m : ℕ) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0)
    (hmiddle : ∀u : fixedPositiveGroup m,coordinates m (f u) 1=coordinates m u 1)
    (u : fixedPositiveGroup m) :
    u⁻¹*f u=centralHom m (Multiplicative.ofAdd (coordinates m (f u) 2-coordinates m u 2)) := by
  let d : Field m := coordinates m (f u) 2-coordinates m u 2
  have hcoords : productCoordinates m (coordinates m u) ![0,0,d]=coordinates m (f u) := by
    funext i
    fin_cases i
    · simpa only [productCoordinates,Matrix.cons_val_zero,add_zero] using (hfirst u).symm
    · simpa only [productCoordinates,Matrix.cons_val_one,Matrix.cons_val_zero,
        add_zero,zero_mul,sub_zero] using (hmiddle u).symm
    · change coordinates m u 2+d-0*coordinates m u 1-0^2*alphaEquiv m (coordinates m u 0)=
        coordinates m (f u) 2
      dsimp only [d]
      ring
  have he : u*centralHom m (Multiplicative.ofAdd d)=f u := by
    calc
      u*centralHom m (Multiplicative.ofAdd d)=
          fixedPositiveChart m (coordinates m u)*fixedPositiveChart m ![0,0,d] :=
        congrArg₂ (fun a b : fixedPositiveGroup m => a*b) (chart_coordinates m u).symm rfl
      _ = fixedPositiveChart m (productCoordinates m (coordinates m u) ![0,0,d]) := chart_mul m _ _
      _ = fixedPositiveChart m (coordinates m (f u)) := congrArg (fixedPositiveChart m) hcoords
      _ = f u := chart_coordinates m (f u)
  change u⁻¹*f u=centralHom m (Multiplicative.ofAdd d)
  calc
    u⁻¹*f u=u⁻¹*(u*centralHom m (Multiplicative.ofAdd d)) :=
      congrArg (fun z : fixedPositiveGroup m => u⁻¹*z) he.symm
    _ = centralHom m (Multiplicative.ofAdd d) := inv_mul_cancel_left _ _

theorem central_difference_mem (m : ℕ) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0)
    (hmiddle : ∀u : fixedPositiveGroup m,coordinates m (f u) 1=coordinates m u 1)
    (u : fixedPositiveGroup m) : u⁻¹*f u∈Subgroup.center (fixedPositiveGroup m) := by
  rw [central_difference_eq m f hfirst hmiddle u,←centralHom_range]
  exact ⟨_,rfl⟩

private def differenceToCenter (m : ℕ) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0)
    (hmiddle : ∀u : fixedPositiveGroup m,coordinates m (f u) 1=coordinates m u 1) :
    fixedPositiveGroup m →* Subgroup.center (fixedPositiveGroup m) :=
  (CFSGCentralCocyclePGroup.centralDifferenceHom f ⊤
    (fun u => central_difference_mem m f hfirst hmiddle u.val)).comp
      (Subgroup.topEquiv : (⊤ : Subgroup (fixedPositiveGroup m)) ≃* fixedPositiveGroup m).symm.toMonoidHom

def centralErrorHom (m : ℕ) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0)
    (hmiddle : ∀u : fixedPositiveGroup m,coordinates m (f u) 1=coordinates m u 1) :
    fixedPositiveGroup m →* Multiplicative (Field m) :=
  (centralEquiv m).symm.toMonoidHom.comp (differenceToCenter m f hfirst hmiddle)

theorem centralError_value (m : ℕ) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0)
    (hmiddle : ∀u : fixedPositiveGroup m,coordinates m (f u) 1=coordinates m u 1)
    (u : fixedPositiveGroup m) : centralHom m (centralErrorHom m f hfirst hmiddle u)=u⁻¹*f u :=
  congrArg (fun z : Subgroup.center (fixedPositiveGroup m) => z.val)
    ((centralEquiv m).apply_symm_apply (differenceToCenter m f hfirst hmiddle u))

theorem centralError_coordinate (m : ℕ) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0)
    (hmiddle : ∀u : fixedPositiveGroup m,coordinates m (f u) 1=coordinates m u 1)
    (u : fixedPositiveGroup m) :
    (centralErrorHom m f hfirst hmiddle u).toAdd=coordinates m (f u) 2-coordinates m u 2 := by
  have he := (centralError_value m f hfirst hmiddle u).trans (central_difference_eq m f hfirst hmiddle u)
  exact congrArg (fun z : Multiplicative (Field m) => z.toAdd) (centralHom_injective m he)

theorem firstKernel_le_centralError_ker (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0)
    (hmiddle : ∀u : fixedPositiveGroup m,coordinates m (f u) 1=coordinates m u 1) :
    firstKernel m≤(centralErrorHom m f hfirst hmiddle).ker := by
  rw [←commutator_eq_firstKernel m hm,commutator_def]
  apply Subgroup.commutator_le.mpr
  intro u _ v _
  change centralErrorHom m f hfirst hmiddle ⁅u,v⁆=1
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

def centralShear (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0)
    (hmiddle : ∀u : fixedPositiveGroup m,coordinates m (f u) 1=coordinates m u 1) : Field m→+Field m where
  toFun a := (factorHom (firstHom m) (firstHom_surjective m) (centralErrorHom m f hfirst hmiddle)
    (firstKernel_le_centralError_ker m hm f hfirst hmiddle) (Multiplicative.ofAdd a)).toAdd
  map_zero' := congrArg (fun z : Multiplicative (Field m) => z.toAdd) (map_one
    (factorHom (firstHom m) (firstHom_surjective m) (centralErrorHom m f hfirst hmiddle)
      (firstKernel_le_centralError_ker m hm f hfirst hmiddle)))
  map_add' a b := congrArg (fun z : Multiplicative (Field m) => z.toAdd) (map_mul
    (factorHom (firstHom m) (firstHom_surjective m) (centralErrorHom m f hfirst hmiddle)
      (firstKernel_le_centralError_ker m hm f hfirst hmiddle)) (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))

theorem centralShear_first (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0)
    (hmiddle : ∀u : fixedPositiveGroup m,coordinates m (f u) 1=coordinates m u 1)
    (u : fixedPositiveGroup m) :
    centralShear m hm f hfirst hmiddle (coordinates m u 0)=coordinates m (f u) 2-coordinates m u 2 := by
  have he := congrArg (fun z : Multiplicative (Field m) => z.toAdd)
    (factorHom_apply (firstHom m) (firstHom_surjective m) (centralErrorHom m f hfirst hmiddle)
      (firstKernel_le_centralError_ker m hm f hfirst hmiddle) u)
  exact he.trans (centralError_coordinate m f hfirst hmiddle u)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoCentralShear
