import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveDerivedMiddleImage

/-! Exact derived subgroup of the literal positive Ree U3 group for
m>=1. Its characteristic two-coordinate layer is precisely a=0. The
proof reconstructs each element from its actual derived c-representative
and its actual central d-correction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveDerivedKernel
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCoordinates CFSGReeGTwoPositiveCentre
open CFSGReeGTwoPositiveFirstQuotient CFSGReeGTwoPositiveCommutatorSeeds
open CFSGReeGTwoPositiveDerivedMiddleImage

theorem commutator_eq_firstKernel (m : ℕ) (hm : 1≤m) :
    commutator (fixedPositiveGroup m)=firstKernel m := by
  apply le_antisymm (commutator_le_firstKernel m)
  intro u hu
  have hu0 := (mem_firstKernel_iff m u).mp hu
  have hi : coordinates m u 1∈middleImage m := by rw [middleImage_eq_top m hm]; trivial
  obtain ⟨v,hv,hc⟩ := (mem_middleImage_iff m _).mp hi
  have hv0 := (mem_firstKernel_iff m v).mp (commutator_le_firstKernel m hv)
  let d : Field m := coordinates m u 2-coordinates m v 2
  have he : v*centralHom m (Multiplicative.ofAdd d)=u := by
    have hcoords : productCoordinates m (coordinates m v) ![0,0,d]=coordinates m u := by
      funext i
      fin_cases i
      · simpa only [productCoordinates,Matrix.cons_val_zero,add_zero] using hv0.trans hu0.symm
      · simpa only [productCoordinates,Matrix.cons_val_one,Matrix.cons_val_zero,
          add_zero,zero_mul,sub_zero] using hc
      · change coordinates m v 2+d-0*coordinates m v 1-0^2*alphaEquiv m (coordinates m v 0)=
          coordinates m u 2
        dsimp only [d]
        ring
    calc
      v*centralHom m (Multiplicative.ofAdd d)=
          fixedPositiveChart m (coordinates m v)*fixedPositiveChart m ![0,0,d] :=
        congrArg₂ (fun x y : fixedPositiveGroup m => x*y) (chart_coordinates m v).symm rfl
      _ = fixedPositiveChart m (productCoordinates m (coordinates m v) ![0,0,d]) := chart_mul m _ _
      _ = fixedPositiveChart m (coordinates m u) := congrArg (fixedPositiveChart m) hcoords
      _ = u := chart_coordinates m u
  exact he ▸ (commutator (fixedPositiveGroup m)).mul_mem hv (centralHom_mem_commutator m d)

theorem chart_mem_commutator_iff (m : ℕ) (hm : 1≤m) (x : Fin 3 → Field m) :
    fixedPositiveChart m x∈commutator (fixedPositiveGroup m) ↔ x 0=0 := by
  rw [commutator_eq_firstKernel m hm,chart_mem_firstKernel_iff]

theorem firstKernel_characteristic (m : ℕ) (hm : 1≤m) : (firstKernel m).Characteristic := by
  rw [←commutator_eq_firstKernel m hm]
  infer_instance

theorem commutator_abelian (m : ℕ) : IsMulCommutative (commutator (fixedPositiveGroup m)) := by
  apply isMulCommutative_iff.mpr
  intro u v
  apply Subtype.ext
  exact firstKernel_commute m u.val v.val
    (commutator_le_firstKernel m u.property) (commutator_le_firstKernel m v.property)

theorem firstHom_surjective (m : ℕ) : Function.Surjective (firstHom m) := by
  intro a
  refine ⟨fixedPositiveChart m ![a.toAdd,0,0],?_⟩
  change Multiplicative.ofAdd (coordinates m (fixedPositiveChart m ![a.toAdd,0,0]) 0)=a
  rw [coordinates_chart]
  rfl

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveDerivedKernel
