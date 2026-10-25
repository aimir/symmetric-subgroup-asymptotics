import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralFirst
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralSecond
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralCancellation
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralFixedAxes

/-! Full actual short positive Levi action on the SAME seven central
coordinates. Active, cancelling and unaffected axes are all discharged
by literal checked parameter identities before homomorphism extensionality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralAction
open CFSGFFourBinaryRadicalCentralLayers CFSGFFourBinaryCentralCoordinateWords
open CFSGFFourBinaryShortLeviCentralFirst CFSGFFourBinaryShortLeviCentralSecond
open CFSGFFourBinaryShortLeviCentralCancellation CFSGFFourBinaryShortLeviCentralFixedAxes
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
private abbrev Raw (K : Type) := K × ((Fin 3 → K) × (Fin 3 → K))
private def node : Fin 2 → Fin 4 := ![0,1]
private def shortShearAdd (K : Type) [Field K] (n : Fin 2) (a : K) : Raw K →+ Raw K where
  toFun x := (x.1,(x.2.1+Pi.single n.succ (a*x.2.1 n.castSucc),
    x.2.2+Pi.single n.castSucc (a*x.2.2 n.succ)))
  map_zero' := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> simp
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change (x.2.1+y.2.1)+Pi.single n.succ (a*(x.2.1 n.castSucc+y.2.1 n.castSucc)) =
          (x.2.1+Pi.single n.succ (a*x.2.1 n.castSucc))+
          (y.2.1+Pi.single n.succ (a*y.2.1 n.castSucc))
        rw [mul_add,Pi.single_add]
        abel
      · change (x.2.2+y.2.2)+Pi.single n.castSucc (a*(x.2.2 n.succ+y.2.2 n.succ)) =
          (x.2.2+Pi.single n.castSucc (a*x.2.2 n.succ))+
          (y.2.2+Pi.single n.castSucc (a*y.2.2 n.succ))
        rw [mul_add,Pi.single_add]
        abel

def shortShear (K : Type) [Field K] (n : Fin 2) (a : K) :
    CentralCoordinates K →* CentralCoordinates K :=
  (shortShearAdd K n a).toMultiplicative

private theorem shortShear_first (K : Type) [Field K] (n : Fin 2) (a t : K) (i : Fin 3) :
    shortShear K n a (Multiplicative.ofAdd (0,(Pi.single i t,0))) =
      Multiplicative.ofAdd (0,(Pi.single i t+
        Pi.single n.succ (a*(Pi.single i t : Fin 3 → K) n.castSucc),0)) := by
  apply Multiplicative.toAdd.injective
  simp [shortShear,shortShearAdd]
private theorem shortShear_second (K : Type) [Field K] (n : Fin 2) (a t : K) (i : Fin 3) :
    shortShear K n a (Multiplicative.ofAdd (0,(0,Pi.single i t))) =
      Multiplicative.ofAdd (0,(0,Pi.single i t+
        Pi.single n.castSucc (a*(Pi.single i t : Fin 3 → K) n.succ))) := by
  apply Multiplicative.toAdd.injective
  simp [shortShear,shortShearAdd]

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

private theorem short_conjugate_first_axis (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a t : K) (i : Fin 3) :
    canonicalRoot realizationData K false (node n) a *
        centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single i t,0))) *
        (canonicalRoot realizationData K false (node n) a)⁻¹ =
      centralMatrixHom K (shortShear K n a (Multiplicative.ofAdd (0,(Pi.single i t,0)))) := by
  rw [shortShear_first]
  by_cases hi : i=n.castSucc
  · subst i
    rw [Pi.single_eq_same]
    exact short_positive_central_first K n a t
  · rw [Pi.single_eq_of_ne (Ne.symm hi),mul_zero,Pi.single_zero,add_zero]
    fin_cases n
    · fin_cases i
      · exact False.elim (hi rfl)
      · exact commute_conjugate _ _ (short_positive_commutes_central_first K 0 a t)
      · exact short_positive_conjugate_extra_first K 0 a t
    · fin_cases i
      · exact short_positive_conjugate_extra_first K 1 a t
      · exact False.elim (hi rfl)
      · exact commute_conjugate _ _ (short_positive_commutes_central_first K 1 a t)

private theorem short_conjugate_second_axis (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a t : K) (i : Fin 3) :
    canonicalRoot realizationData K false (node n) a *
        centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single i t))) *
        (canonicalRoot realizationData K false (node n) a)⁻¹ =
      centralMatrixHom K (shortShear K n a (Multiplicative.ofAdd (0,(0,Pi.single i t)))) := by
  rw [shortShear_second]
  by_cases hi : i=n.succ
  · subst i
    rw [Pi.single_eq_same]
    exact short_positive_central_second K n a t
  · rw [Pi.single_eq_of_ne (Ne.symm hi),mul_zero,Pi.single_zero,add_zero]
    fin_cases n
    · fin_cases i
      · exact commute_conjugate _ _ (short_positive_commutes_central_second K 0 a t)
      · exact False.elim (hi rfl)
      · exact short_positive_conjugate_extra_second K 0 a t
    · fin_cases i
      · exact short_positive_conjugate_extra_second K 1 a t
      · exact commute_conjugate _ _ (short_positive_commutes_central_second K 1 a t)
      · exact False.elim (hi rfl)

theorem short_positive_central_action (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (a : K) (x : CentralCoordinates K) :
    canonicalRoot realizationData K false (node n) a * centralMatrixHom K x *
      (canonicalRoot realizationData K false (node n) a)⁻¹ =
        centralMatrixHom K (shortShear K n a x) := by
  let g := canonicalRoot realizationData K false (node n) a
  have hh : (MulAut.conj g).toMonoidHom.comp (centralMatrixHom K) =
      (centralMatrixHom K).comp (shortShear K n a) := by
    apply seven_axis_ext
    · intro c
      change g*centralMatrixHom K (Multiplicative.ofAdd (c,(0,0)))*g⁻¹ =
        centralMatrixHom K (shortShear K n a (Multiplicative.ofAdd (c,(0,0))))
      have he : shortShear K n a (Multiplicative.ofAdd (c,(0,0))) =
          Multiplicative.ofAdd (c,(0,0)) := by
        apply Multiplicative.toAdd.injective
        simp [shortShear,shortShearAdd]
      rw [he]
      exact commute_conjugate _ _ (short_positive_commutes_central_scalar K n a c)
    · intro i t
      exact short_conjugate_first_axis K n a t i
    · intro i t
      exact short_conjugate_second_axis K n a t i
  exact DFunLike.congr_fun hh x

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviCentralAction
