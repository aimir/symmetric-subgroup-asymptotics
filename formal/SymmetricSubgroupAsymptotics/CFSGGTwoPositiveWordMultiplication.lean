import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalHigherCollecting
import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveSixWord

/-! The literal six-root chart is closed under multiplication in
characteristic three. The collection is performed in an abstract group
before specializing to the SAME original Model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordMultiplication
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveRootWords CFSGGTwoPositiveSixWord
open CFSGGTwoOriginalPositiveCollecting CFSGGTwoOriginalHigherCollecting

variable {R : Type*} [Ring R]

def shortShift (a : R) (x : Fin 4 → R) : Fin 4 → R :=
  ![x 0,x 1-a*x 0,x 2,x 3]

def longShift (b : R) (x : Fin 4 → R) : Fin 4 → R :=
  ![x 0,x 1,x 2,x 3+b*x 2]

def correction (a b : R) : Fin 4 → R :=
  ![-a*b,-a^2*b,-a^3*b,a^3*b^2]

private theorem multiply_heads {G : Type*} [Group G]
    (u v : R → G) (H : (Fin 4 → R) → G)
    (hu : ∀ a b, u a*u b=u (a+b)) (hv : ∀ a b, v a*v b=v (a+b))
    (hH : ∀ x y, H x*H y=H (x+y))
    (hs : ∀ x a, H x*u a=u a*H (shortShift a x))
    (hl : ∀ x b, H x*v b=v b*H (longShift b x))
    (hc : ∀ a b, v b*u a=u a*v b*H (correction a b))
    (a b A B : R) (x y : Fin 4 → R) :
    (u a*v b*H x)*(u A*v B*H y) =
      u (a+A)*v (b+B)*H (longShift B (correction A b+shortShift A x)+y) := by
  calc
    _ = u a*v b*(H x*u A)*v B*H y := by simp only [mul_assoc]
    _ = u a*v b*(u A*H (shortShift A x))*v B*H y := by rw [hs]
    _ = u a*(v b*u A)*H (shortShift A x)*v B*H y := by simp only [mul_assoc]
    _ = u a*(u A*v b*H (correction A b))*H (shortShift A x)*v B*H y := by rw [hc]
    _ = (u a*u A)*v b*(H (correction A b)*H (shortShift A x))*v B*H y := by
      simp only [mul_assoc]
    _ = u (a+A)*v b*H (correction A b+shortShift A x)*v B*H y := by rw [hu,hH]
    _ = u (a+A)*v b*(H (correction A b+shortShift A x)*v B)*H y := by
      simp only [mul_assoc]
    _ = u (a+A)*v b*(v B*H (longShift B (correction A b+shortShift A x)))*H y := by
      rw [hl]
    _ = u (a+A)*(v b*v B)*(H (longShift B (correction A b+shortShift A x))*H y) := by
      simp only [mul_assoc]
    _ = _ := by rw [hv,hH]

variable (K : Type) [Field K] [CharP K 3]

def tailCoordinates (x : Fin 6 → K) : Fin 4 → K := ![x 2,x 3,x 4,x 5]

/-- Exact coordinates, including the final mixed long-root contribution. -/
def productCoordinates (x y : Fin 6 → K) : Fin 6 → K :=
  ![x 0+y 0,x 1+y 1,x 2+y 2-y 0*x 1,
    x 3+y 3-y 0*x 2-(y 0)^2*x 1,
    x 4+y 4-(y 0)^3*x 1,
    x 5+y 5+(y 0)^3*(x 1)^2+y 1*(x 4-(y 0)^3*x 1)]

private theorem higherWord_four (a b c d : K) :
    higherWord K ![a,b,c,d]=positiveModel K 2 a*positiveModel K 3 b*
      positiveModel K 4 c*positiveModel K 5 d := rfl

private theorem modelWord_split (x : Fin 6 → K) :
    modelWord K x=positiveModel K 0 (x 0)*positiveModel K 1 (x 1)*
      higherWord K (tailCoordinates K x) := by
  simp only [tailCoordinates,higherWord_four,modelWord,mul_assoc]

private theorem simple_collecting_tail (a b : K) :
    positiveModel K 1 b*positiveModel K 0 a=
      positiveModel K 0 a*positiveModel K 1 b*higherWord K (correction a b) := by
  rw [simple_collecting]
  simp only [correction,higherWord_four,mul_assoc]

private theorem collected_tail (x y : Fin 6 → K) :
    longShift (y 1) (correction (y 0) (x 1)+shortShift (y 0) (tailCoordinates K x))+
      tailCoordinates K y=tailCoordinates K (productCoordinates K x y) := by
  funext i
  fin_cases i
  · change -(y 0)*x 1+x 2+y 2=x 2+y 2-y 0*x 1
    ring
  · change -(y 0)^2*x 1+(x 3-y 0*x 2)+y 3=
      x 3+y 3-y 0*x 2-(y 0)^2*x 1
    ring
  · change -(y 0)^3*x 1+x 4+y 4=x 4+y 4-(y 0)^3*x 1
    ring
  · change (y 0)^3*(x 1)^2+x 5+y 1*(-(y 0)^3*x 1+x 4)+y 5=
      x 5+y 5+(y 0)^3*(x 1)^2+y 1*(x 4-(y 0)^3*x 1)
    ring

theorem modelWord_mul (x y : Fin 6 → K) :
    modelWord K x*modelWord K y=modelWord K (productCoordinates K x y) := by
  have h := multiply_heads (positiveModel K 0) (positiveModel K 1) (higherWord K)
    (positiveModel_add K 0) (positiveModel_add K 1) (higherWord_add K)
    (higherWord_short K) (higherWord_long K) (simple_collecting_tail K)
    (x 0) (x 1) (y 0) (y 1) (tailCoordinates K x) (tailCoordinates K y)
  calc
    _ = (positiveModel K 0 (x 0)*positiveModel K 1 (x 1)*higherWord K (tailCoordinates K x))*
      (positiveModel K 0 (y 0)*positiveModel K 1 (y 1)*higherWord K (tailCoordinates K y)) := by
      rw [modelWord_split,modelWord_split]
    _ = positiveModel K 0 (x 0+y 0)*positiveModel K 1 (x 1+y 1)*
      higherWord K (longShift (y 1)
        (correction (y 0) (x 1)+shortShift (y 0) (tailCoordinates K x))+tailCoordinates K y) := h
    _ = positiveModel K 0 (x 0+y 0)*positiveModel K 1 (x 1+y 1)*
      higherWord K (tailCoordinates K (productCoordinates K x y)) := by rw [collected_tail]
    _ = _ := (modelWord_split K (productCoordinates K x y)).symm

end SymmetricSubgroupAsymptotics.CFSGGTwoPositiveWordMultiplication
