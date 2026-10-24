import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralFixedAxes
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralCoordinates

/-! Full actual positive-long Levi covariance on the same seven central
coordinates. The shear is additive in characteristic two; no K-linearity
is asserted here, and its literal square term is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralAction
open CFSGFFourBinaryRadicalCentralLayers CFSGFFourBinaryCentralCoordinateWords
open CFSGFFourBinaryLongLeviCentralCoordinates CFSGFFourBinaryLongLeviCentralFixedAxes
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix

private theorem square_add {K : Type} [CommRing K] [CharP K 2] (x y : K) :
    (x+y)^2=x^2+y^2 := by
  calc
    (x+y)^2=x^2+y^2+(x*y+x*y) := by ring
    _=x^2+y^2 := by rw [CharTwo.add_self_eq_zero,add_zero]

private abbrev Raw (K : Type) := K × ((Fin 3 → K) × (Fin 3 → K))

private def longShearAdd (K : Type) [Field K] [CharP K 2] (a : K) : Raw K →+ Raw K where
  toFun x := (x.1+a*(x.2.1 2)^2,(x.2.1,x.2.2+Pi.single 2 (a*x.2.1 2)))
  map_zero' := by
    change ((0 : K)+a*0^2,((0 : Fin 3 → K),(0 : Fin 3 → K)+Pi.single (2 : Fin 3) (a*0)))=(0,(0,0))
    simp
  map_add' x y := by
    apply Prod.ext
    · change x.1+y.1+a*(x.2.1 2+y.2.1 2)^2 =
        (x.1+a*(x.2.1 2)^2)+(y.1+a*(y.2.1 2)^2)
      rw [square_add]
      ring
    · apply Prod.ext
      · rfl
      · change (x.2.2+y.2.2)+Pi.single 2 (a*(x.2.1 2+y.2.1 2)) =
          (x.2.2+Pi.single 2 (a*x.2.1 2))+(y.2.2+Pi.single 2 (a*y.2.1 2))
        rw [mul_add,Pi.single_add]
        abel

def longShear (K : Type) [Field K] [CharP K 2] (a : K) :
    CentralCoordinates K →* CentralCoordinates K :=
  (longShearAdd K a).toMultiplicative

private theorem seven_axis_ext {K G : Type} [AddCommGroup K] [Group G]
    (f g : Multiplicative (Raw K) →* G)
    (hc : ∀ c, f (Multiplicative.ofAdd (c,(0,0)))=g (Multiplicative.ofAdd (c,(0,0))))
    (hu : ∀ (i : Fin 3) t, f (Multiplicative.ofAdd (0,(Pi.single i t,0)))=
      g (Multiplicative.ofAdd (0,(Pi.single i t,0))))
    (hv : ∀ (i : Fin 3) t, f (Multiplicative.ofAdd (0,(0,Pi.single i t)))=
      g (Multiplicative.ofAdd (0,(0,Pi.single i t)))) : f=g := by
  apply MonoidHom.ext
  intro x
  let c := x.toAdd.1
  let u := x.toAdd.2.1
  let v := x.toAdd.2.2
  have hu0 : u=Pi.single 0 (u 0)+Pi.single 1 (u 1)+Pi.single 2 (u 2) := by
    funext i
    fin_cases i <;> simp
  have hv0 : v=Pi.single 0 (v 0)+Pi.single 1 (v 1)+Pi.single 2 (v 2) := by
    funext i
    fin_cases i <;> simp
  have he : x =
      Multiplicative.ofAdd (c,(0,0)) *
      Multiplicative.ofAdd (0,(Pi.single (0 : Fin 3) (u 0),0)) *
      Multiplicative.ofAdd (0,(Pi.single (1 : Fin 3) (u 1),0)) *
      Multiplicative.ofAdd (0,(Pi.single (2 : Fin 3) (u 2),0)) *
      Multiplicative.ofAdd (0,(0,Pi.single (0 : Fin 3) (v 0))) *
      Multiplicative.ofAdd (0,(0,Pi.single (1 : Fin 3) (v 1))) *
      Multiplicative.ofAdd (0,(0,Pi.single (2 : Fin 3) (v 2))) := by
    apply Multiplicative.toAdd.injective
    change (c,(u,v)) =
      (c,(0,0))+(0,(Pi.single 0 (u 0),0))+(0,(Pi.single 1 (u 1),0))+
      (0,(Pi.single 2 (u 2),0))+(0,(0,Pi.single 0 (v 0)))+
      (0,(0,Pi.single 1 (v 1)))+(0,(0,Pi.single 2 (v 2)))
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simpa using hu0
      · simpa using hv0
  calc
    f x = f (Multiplicative.ofAdd (c,(0,0))) *
        f (Multiplicative.ofAdd (0,(Pi.single (0 : Fin 3) (u 0),0))) *
        f (Multiplicative.ofAdd (0,(Pi.single (1 : Fin 3) (u 1),0))) *
        f (Multiplicative.ofAdd (0,(Pi.single (2 : Fin 3) (u 2),0))) *
        f (Multiplicative.ofAdd (0,(0,Pi.single (0 : Fin 3) (v 0)))) *
        f (Multiplicative.ofAdd (0,(0,Pi.single (1 : Fin 3) (v 1)))) *
        f (Multiplicative.ofAdd (0,(0,Pi.single (2 : Fin 3) (v 2)))) := by
      rw [he,map_mul,map_mul,map_mul,map_mul,map_mul,map_mul]
    _ = g (Multiplicative.ofAdd (c,(0,0))) *
        g (Multiplicative.ofAdd (0,(Pi.single (0 : Fin 3) (u 0),0))) *
        g (Multiplicative.ofAdd (0,(Pi.single (1 : Fin 3) (u 1),0))) *
        g (Multiplicative.ofAdd (0,(Pi.single (2 : Fin 3) (u 2),0))) *
        g (Multiplicative.ofAdd (0,(0,Pi.single (0 : Fin 3) (v 0)))) *
        g (Multiplicative.ofAdd (0,(0,Pi.single (1 : Fin 3) (v 1)))) *
        g (Multiplicative.ofAdd (0,(0,Pi.single (2 : Fin 3) (v 2)))) := by
      rw [hc,hu,hu,hu,hv,hv,hv]
    _ = g x := by rw [he,map_mul,map_mul,map_mul,map_mul,map_mul,map_mul]

private theorem commute_conjugate {G : Type} [Group G] (g x : G) (h : Commute g x) :
    g*x*g⁻¹=x := by
  rw [h.eq]
  group

theorem long_positive_central_action (K : Type) [Field K] [CharP K 2]
    (a : K) (x : CentralCoordinates K) :
    canonicalRoot realizationData K false 2 a * centralMatrixHom K x *
      (canonicalRoot realizationData K false 2 a)⁻¹ =
        centralMatrixHom K (longShear K a x) := by
  let g := canonicalRoot realizationData K false 2 a
  have hh : (MulAut.conj g).toMonoidHom.comp (centralMatrixHom K) =
      (centralMatrixHom K).comp (longShear K a) := by
    apply seven_axis_ext
    · intro c
      change g*centralMatrixHom K (Multiplicative.ofAdd (c,(0,0)))*g⁻¹ =
        centralMatrixHom K (longShear K a (Multiplicative.ofAdd (c,(0,0))))
      have hp : longShear K a (Multiplicative.ofAdd (c,(0,0))) =
          Multiplicative.ofAdd (c,(0,0)) := by
        apply Multiplicative.toAdd.injective
        change (c+a*0^2,((0 : Fin 3 → K),(0 : Fin 3 → K)+Pi.single (2 : Fin 3) (a*0)))=(c,(0,0))
        simp
      rw [hp]
      exact commute_conjugate _ _ (long_positive_commutes_central_scalar K a c)
    · intro i t
      change g*centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single i t,0)))*g⁻¹ =
        centralMatrixHom K (longShear K a (Multiplicative.ofAdd (0,(Pi.single i t,0))))
      by_cases hi : i=2
      · subst i
        have hp : longShear K a (Multiplicative.ofAdd (0,(Pi.single (2 : Fin 3) t,0))) =
            Multiplicative.ofAdd (a*t^2,(Pi.single (2 : Fin 3) t,Pi.single (2 : Fin 3) (a*t))) := by
          apply Multiplicative.toAdd.injective
          change ((0 : K)+a*((Pi.single (2 : Fin 3) t : Fin 3 → K) 2)^2,
            ((Pi.single (2 : Fin 3) t : Fin 3 → K),(0 : Fin 3 → K)+
              Pi.single (2 : Fin 3) (a*(Pi.single (2 : Fin 3) t : Fin 3 → K) 2))) = _
          simp
        rw [hp]
        exact long_positive_central_first K a t
      · have hz : (Pi.single i t : Fin 3 → K) (2 : Fin 3)=0 := by simp [Pi.single_apply,hi,Ne.symm hi]
        have hp : longShear K a (Multiplicative.ofAdd (0,(Pi.single i t,0))) =
            Multiplicative.ofAdd (0,(Pi.single i t,0)) := by
          apply Multiplicative.toAdd.injective
          change ((0 : K)+a*((Pi.single i t : Fin 3 → K) 2)^2,
            ((Pi.single i t : Fin 3 → K),(0 : Fin 3 → K)+
              Pi.single (2 : Fin 3) (a*(Pi.single i t : Fin 3 → K) 2))) = _
          rw [hz]
          simp
        rw [hp]
        exact commute_conjugate _ _ (long_positive_commutes_central_first K i hi a t)
    · intro i t
      change g*centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single i t)))*g⁻¹ =
        centralMatrixHom K (longShear K a (Multiplicative.ofAdd (0,(0,Pi.single i t))))
      have hp : longShear K a (Multiplicative.ofAdd (0,(0,Pi.single i t))) =
          Multiplicative.ofAdd (0,(0,Pi.single i t)) := by
        apply Multiplicative.toAdd.injective
        change ((0 : K)+a*0^2,((0 : Fin 3 → K),(Pi.single i t : Fin 3 → K)+Pi.single (2 : Fin 3) (a*0)))=(0,(0,Pi.single i t))
        simp
      rw [hp]
      exact commute_conjugate _ _ (long_positive_commutes_central_second K i a t)
  exact DFunLike.congr_fun hh x

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryLongLeviCentralAction
