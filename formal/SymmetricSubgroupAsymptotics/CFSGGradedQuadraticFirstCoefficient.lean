import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSingleDegreeSpan

/-! A first homogeneous coefficient in a quadratic matrix unit can be
recovered by literal lattice-degree projection. Distinct root degrees
cannot hide that coefficient in another root's quadratic term, even in
bad coefficient characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedQuadraticFirstCoefficient
open CFSGGradedMatrixSupport CFSGGradedMatrixSingleDegreeSpan
variable {I K V : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    [AddCommGroup V] [DecidableEq V]

theorem degreePart_one_zero (weight : I→V) (d : V) (hd : d≠0) :
    degreePart weight d (1 : Matrix I I K)=0 :=
  degreePart_zero_of_other weight d 0 1
    (by simpa only [add_zero] using supported_one (R:=K) weight) hd

theorem degreePart_quadratic (weight : I→V) (d : V) (E D : Matrix I I K)
    (hE : Supported weight (fun v=>v+d) E)
    (hD : Supported weight (fun v=>v+(d+d)) D) (hd : d≠0) (hdd : d≠d+d) :
    degreePart weight d (1+E+D)=E := by
  rw [map_add,map_add,degreePart_one_zero weight d hd,
    degreePart_eq weight d E hE,degreePart_zero_of_other weight d (d+d) D hD hdd,
    zero_add,add_zero]

theorem first_zero_of_distinct_quadratic (weight : I→V) (d e : V)
    (E D F G : Matrix I I K)
    (hE : Supported weight (fun v=>v+d) E)
    (hD : Supported weight (fun v=>v+(d+d)) D)
    (hF : Supported weight (fun v=>v+e) F)
    (hG : Supported weight (fun v=>v+(e+e)) G)
    (hd : d≠0) (hdd : d≠d+d) (hde : d≠e) (hde2 : d≠e+e)
    (h : (1 : Matrix I I K)+E+D=1+F+G) : E=0 := by
  have hh := congrArg (degreePart weight d) h
  rw [degreePart_quadratic weight d E D hE hD hd hdd] at hh
  rw [map_add,map_add,degreePart_one_zero weight d hd,
    degreePart_zero_of_other weight d e F hF hde,
    degreePart_zero_of_other weight d (e+e) G hG hde2,zero_add,add_zero] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGGradedQuadraticFirstCoefficient
