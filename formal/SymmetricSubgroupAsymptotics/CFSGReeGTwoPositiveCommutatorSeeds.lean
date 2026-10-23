import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveFirstQuotient
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-! Actual U3 commutators fill its whole centre. Their c-coordinates
contain a nonzero skew-alpha product for every m>=1. These are literal
chart identities; no rank, order or ambient-derived assumption is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCommutatorSeeds
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCoordinates CFSGReeGTwoPositiveCentre
open CFSGReeGTwoPositiveFirstQuotient CFSGReeGTwoOriginalTorus
open CFSGReeGTwoFixedTorusRegularity CFSGGTwoNaturalPositiveTorusAction
open scoped commutatorElement

theorem middle_first_commutator (m : ℕ) (c a : Field m) :
    ⁅fixedPositiveChart m ![0,c,0],fixedPositiveChart m ![a,0,0]⁆=
      centralHom m (Multiplicative.ofAdd (-a*c)) := by
  have he : fixedPositiveChart m ![0,c,0]*fixedPositiveChart m ![a,0,0]=
      centralHom m (Multiplicative.ofAdd (-a*c))*
        (fixedPositiveChart m ![a,0,0]*fixedPositiveChart m ![0,c,0]) := by
    change fixedPositiveChart m ![0,c,0]*fixedPositiveChart m ![a,0,0]=
      fixedPositiveChart m ![0,0,-a*c]*
        (fixedPositiveChart m ![a,0,0]*fixedPositiveChart m ![0,c,0])
    rw [chart_mul,chart_mul,chart_mul]
    apply congrArg (fixedPositiveChart m)
    funext i
    fin_cases i <;> simp [productCoordinates]
  rw [commutatorElement_def,he]
  group

theorem centralHom_mem_commutator (m : ℕ) (d : Field m) :
    centralHom m (Multiplicative.ofAdd d)∈commutator (fixedPositiveGroup m) := by
  have hh : ⁅fixedPositiveChart m ![0,-d,0],fixedPositiveChart m ![1,0,0]⁆∈
      commutator (fixedPositiveGroup m) :=
    Subgroup.commutator_mem_commutator (by trivial) (by trivial)
  rw [middle_first_commutator] at hh
  simpa only [neg_mul_neg,one_mul] using hh

theorem center_le_commutator (m : ℕ) :
    Subgroup.center (fixedPositiveGroup m)≤commutator (fixedPositiveGroup m) := by
  rw [←centralHom_range]
  rintro u ⟨d,rfl⟩
  exact centralHom_mem_commutator m d.toAdd

theorem first_first_commutator_middle (m : ℕ) (a b : Field m) :
    coordinates m ⁅fixedPositiveChart m ![a,0,0],fixedPositiveChart m ![b,0,0]⁆ 1=
      a*alphaEquiv m b-b*alphaEquiv m a := by
  let u := ⁅fixedPositiveChart m ![a,0,0],fixedPositiveChart m ![b,0,0]⁆
  have hu : u∈commutator (fixedPositiveGroup m) :=
    Subgroup.commutator_mem_commutator (by trivial) (by trivial)
  have hzero : coordinates m u 0=0 :=
    (mem_firstKernel_iff m u).mp (commutator_le_firstKernel m hu)
  have he : u*(fixedPositiveChart m ![b,0,0]*fixedPositiveChart m ![a,0,0])=
      fixedPositiveChart m ![a,0,0]*fixedPositiveChart m ![b,0,0] := by
    dsimp only [u]
    rw [commutatorElement_def]
    group
  have hh := congrArg (coordinates m) he
  simp only [coordinates_mul,coordinates_chart] at hh
  have hc : coordinates m u 1-a*alphaEquiv m b = -b*alphaEquiv m a := by
    simpa [productCoordinates,hzero,sub_eq_add_neg] using congrFun hh 1
  change coordinates m u 1=_
  calc
    coordinates m u 1=(coordinates m u 1-a*alphaEquiv m b)+a*alphaEquiv m b := by ring
    _ = -b*alphaEquiv m a+a*alphaEquiv m b := by rw [hc]
    _ = a*alphaEquiv m b-b*alphaEquiv m a := by ring

theorem exists_nonzero_commutator_middle (m : ℕ) (hm : 1≤m) :
    ∃ u : fixedPositiveGroup m,u∈commutator (fixedPositiveGroup m) ∧ coordinates m u 1≠0 := by
  obtain ⟨t,ht,htn⟩ := exists_regular_unit m hm
  have hne : alpha m (t : Field m)≠(t : Field m) := by
    intro he
    have hu : unitsAlpha m t=t := Units.ext he
    apply rootScale_two_ne_one m t ht htn
    change ((t⁻¹*unitsAlpha m t : (Field m)ˣ) : Field m)=1
    rw [hu,inv_mul_cancel]
    rfl
  refine ⟨⁅fixedPositiveChart m ![1,0,0],fixedPositiveChart m ![(t : Field m),0,0]⁆,
    Subgroup.commutator_mem_commutator (by trivial) (by trivial),?_⟩
  rw [first_first_commutator_middle]
  simpa only [map_one,one_mul,mul_one,alphaEquiv_apply,sub_ne_zero] using hne

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCommutatorSeeds
