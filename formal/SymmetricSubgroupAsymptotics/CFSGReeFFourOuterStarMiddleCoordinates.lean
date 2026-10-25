import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarConjugation

/-! The literal four-coordinate middle words, in the orientation imposed
by the selected E6 root slice. This is only a coordinate identity; the
whole fixed head and its higher corrections are not identified here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarMiddleCoordinates
open CFSGReeFFourOuterStarConjugation

private abbrev C (K : Type) [Field K] (j : Fin 3) : AddAut (Fin 4 → K) :=
  shearCoordinates K j 1
private abbrev S (K : Type) [Field K] (j : Fin 3) : AddAut (Fin 4 → K) :=
  swapCoordinates K j

private theorem swap_inverse (K : Type) [Field K] (j : Fin 3) :
    (S K j)⁻¹=S K j := by
  ext v k
  rfl

def coordinateY (K : Type) [Field K] : AddAut (Fin 4 → K) :=
  C K 0*C K 2*C K 1*((S K 0*S K 2)*C K 1*(S K 0*S K 2)⁻¹)

def coordinateW (K : Type) [Field K] : AddAut (Fin 4 → K) :=
  S K 0*S K 2*S K 1*S K 0*S K 2*S K 1

def coordinateR (K : Type) [Field K] : AddAut (Fin 4 → K) :=
  coordinateW K*(coordinateY K)^2

theorem coordinateY_apply (K : Type) [Field K] (v : Fin 4 → K) :
    coordinateY K v = ![v 0,v 0+v 1,v 1+v 2,v 0+v 1+v 2+v 3] := by
  ext k
  fin_cases k <;>
    simp [coordinateY,mul_inv_rev,AddAut.mul_apply,C,S,
      shearCoordinates_apply,swapCoordinates,Pi.single_apply,Equiv.swap_apply_def] <;> abel

theorem coordinateW_apply (K : Type) [Field K] (v : Fin 4 → K) :
    coordinateW K v = ![v 3,v 2,v 1,v 0] := by
  ext k
  fin_cases k <;>
    simp [coordinateW,AddAut.mul_apply,S,swapCoordinates,Equiv.swap_apply_def]

theorem selected_Y_eq_R (K : Type) [Field K] [CharP K 2] (a : K) :
    coordinateY K (Pi.single 0 a)=coordinateR K (Pi.single 0 a) := by
  simp only [coordinateR,pow_two,AddAut.mul_apply,coordinateY_apply,coordinateW_apply]
  ext k
  fin_cases k <;> simp [CharTwo.add_self_eq_zero]

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarMiddleCoordinates
