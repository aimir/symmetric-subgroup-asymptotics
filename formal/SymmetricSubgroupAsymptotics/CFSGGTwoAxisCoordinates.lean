import SymmetricSubgroupAsymptotics.CFSGGTwoInvariantAxis
import SymmetricSubgroupAsymptotics.CFSGGTwoD4Inclusion
import SymmetricSubgroupAsymptotics.CFSGSplitOddSingularPointCardinality

/-! The actual hyperplane perpendicular to the fixed G2 axis has seven
coordinates, and its quadratic zero cone has a literal hyperbolic-pair
chart with five residual coordinates. No original projective action is
inferred from these natural coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoAxisCoordinates
open CFSGGTwoSerreMatrices CFSGGTwoInvariantAxis CFSGGTwoD4Inclusion
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexPolarForm CFSGSplitOddSingularPointCardinality
variable (K : Type) [Field K]

def axisHyperplane : Submodule K (Index→K) where
  carrier := {v | v (pos 3)=v (neg 3)}
  zero_mem' := rfl
  add_mem' := by
    intro v w hv hw
    change v (pos 3)=v (neg 3) at hv
    change w (pos 3)=w (neg 3) at hw
    change v (pos 3)+w (pos 3)=v (neg 3)+w (neg 3)
    rw [hv,hw]
  smul_mem' := by
    intro a v hv
    change v (pos 3)=v (neg 3) at hv
    change a • v (pos 3)=a • v (neg 3)
    rw [hv]

theorem polar_axis (v : Index→K) : polar K (axis K) v=v (neg 3)-v (pos 3) := by
  simp [polar,leftPart,rightPart,dotProduct,Fin.sum_univ_succ,axis,pos,neg,Fin.ext_iff,
    sub_eq_add_neg]

theorem natural_preserves_hyperplane (g : naturalGroup K) (v : axisHyperplane K) :
    (g.val:Mat K)*ᵥv.val∈axisHyperplane K := by
  have hh := elementary_preserves_polar K 0 (naturalIntoD4 K g) (axis K) v.val
  change polar K ((g.val:Mat K)*ᵥaxis K) ((g.val:Mat K)*ᵥv.val)=polar K (axis K) v.val at hh
  rw [natural_fixes_axis,polar_axis,polar_axis] at hh
  have hz : v.val (neg 3)-v.val (pos 3)=0 := by rw [v.property,sub_self]
  change ((g.val:Mat K)*ᵥv.val) (pos 3)=((g.val:Mat K)*ᵥv.val) (neg 3)
  exact (sub_eq_zero.mp (hh.trans hz)).symm

def middle (v : axisHyperplane K) : Fin 5→K :=
  ![v.val (pos 1),v.val (pos 2),v.val (neg 1),v.val (neg 2),v.val (pos 3)]

def coordinates (v : axisHyperplane K) : K×(Fin 5→K)×K :=
  (v.val (pos 0),middle K v,v.val (neg 0))

theorem coordinates_injective : Function.Injective (coordinates K) := by
  intro v w he
  have hfirst := congrArg (fun x : K×(Fin 5→K)×K=>x.1) he
  have hmiddle := congrArg (fun x : K×(Fin 5→K)×K=>x.2.1) he
  have hlast := congrArg (fun x : K×(Fin 5→K)×K=>x.2.2) he
  dsimp only [coordinates] at hfirst hmiddle hlast
  have hm (i : Fin 5) := congrFun hmiddle i
  have hfour : v.val (pos 3)=w.val (pos 3) := by simpa [middle,pos] using hm 4
  apply Subtype.ext
  funext x
  rcases x with i|i <;> fin_cases i
  · exact hfirst
  · simpa [middle,pos] using hm 0
  · simpa [middle,pos] using hm 1
  · exact hfour
  · exact hlast
  · simpa [middle,neg] using hm 2
  · simpa [middle,neg] using hm 3
  · exact v.property.symm.trans (hfour.trans w.property)

def residualQ (w : Fin 5→K) : K := w 0*w 2+w 1*w 3+w 4*w 4

theorem norm_coordinates (v : axisHyperplane K) :
    splitQuadraticForm K 4 v.val=v.val (pos 0)*v.val (neg 0)+residualQ K (middle K v) := by
  rw [splitQuadraticForm_apply]
  simp only [splitQ,leftPart,rightPart,dotProduct,Fin.sum_univ_succ,Function.comp_apply]
  change v.val (pos 0)*v.val (neg 0)+(v.val (pos 1)*v.val (neg 1)+
    (v.val (pos 2)*v.val (neg 2)+(v.val (pos 3)*v.val (neg 3)+0)))=_
  rw [←v.property]
  simp [residualQ,middle]
  ring

theorem zero_vectors_card_le [Finite K] :
    Nat.card {v : axisHyperplane K // splitQuadraticForm K 4 v.val=0}≤2*Nat.card K^6 := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (zeroCone (residualQ K)) := by unfold zeroCone;infer_instance
  let encode : {v : axisHyperplane K // splitQuadraticForm K 4 v.val=0}→zeroCone (residualQ K) :=
    fun v=>⟨coordinates K v.val,by
      change v.val.val (pos 0)*v.val.val (neg 0)+residualQ K (middle K v.val)=0
      rw [←norm_coordinates]
      exact v.property⟩
  have hinj : Function.Injective encode := by
    intro v w he
    apply Subtype.ext
    apply coordinates_injective K
    exact congrArg Subtype.val he
  calc
    _≤Nat.card (zeroCone (residualQ K)) := Nat.card_le_card_of_injective encode hinj
    _≤2*Nat.card K*Nat.card (Fin 5→K) := zeroCone_card_le (residualQ K)
    _=2*Nat.card K^6 := by rw [Nat.card_fun,Nat.card_fin];ring

end SymmetricSubgroupAsymptotics.CFSGGTwoAxisCoordinates
