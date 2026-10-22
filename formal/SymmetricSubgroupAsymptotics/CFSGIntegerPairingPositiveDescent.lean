import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Elementary integer-lattice descent facts. A nonnegative vector of
positive norm has a positively paired coordinate. Norm four or six cannot
be supported on one norm-two coordinate axis. These are literal bilinear
identities, with no finite-root-system or Lie recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGIntegerPairingPositiveDescent
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem norm_coordinate_sum (B : LinearMap.BilinForm ℤ (I→ℤ)) (x : I→ℤ) :
    B x x=∑i,x i*B x (Pi.single i (1:ℤ) : I→ℤ) := by
  have hx : (∑i,x i • (Pi.single i (1:ℤ) : I→ℤ))=x := by
    calc
      _=∑i,(Pi.single i (x i) : I→ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        funext j
        by_cases hij : i=j <;> simp [Pi.smul_apply,Pi.single_apply,smul_eq_mul,hij]
      _=x := LinearMap.sum_single_apply (fun _ : I=>ℤ) x
  calc
    _=B x (∑i,x i • (Pi.single i (1:ℤ) : I→ℤ)) := congrArg (B x) hx.symm
    _=_ := by simp only [map_sum,map_smul,smul_eq_mul]

theorem exists_positive_coordinate_pairing (B : LinearMap.BilinForm ℤ (I→ℤ))
    (x : I→ℤ) (hx : ∀i,0≤x i) (hnorm : 0<B x x) :
    ∃i,0<x i ∧ 0<B x (Pi.single i (1:ℤ) : I→ℤ) := by
  have hp : ∃i,0<x i*B x (Pi.single i (1:ℤ) : I→ℤ) := by
    by_contra hn
    have hs : (∑i,x i*B x (Pi.single i (1:ℤ) : I→ℤ))≤0 := by
      apply Finset.sum_nonpos
      intro i hi
      exact le_of_not_gt (fun h=>hn ⟨i,h⟩)
    rw [←norm_coordinate_sum B x] at hs
    omega
  obtain ⟨i,hi⟩ := hp
  refine ⟨i,?_,?_⟩
  · by_contra hn
    have hz : x i=0 := by have := hx i;omega
    rw [hz,zero_mul] at hi
    omega
  · by_contra hn
    have hn' : B x (Pi.single i (1:ℤ) : I→ℤ)≤0 := le_of_not_gt hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (hx i) hn'
    omega

omit [Fintype I] in
theorem norm_four_or_six_not_axis (B : LinearMap.BilinForm ℤ (I→ℤ)) (i : I)
    (hii : B (Pi.single i (1:ℤ) : I→ℤ) (Pi.single i (1:ℤ) : I→ℤ)=2)
    (m : ℤ) (hm : 0≤m) :
    B (m • (Pi.single i (1:ℤ) : I→ℤ)) (m • (Pi.single i (1:ℤ) : I→ℤ))≠4 ∧
      B (m • (Pi.single i (1:ℤ) : I→ℤ)) (m • (Pi.single i (1:ℤ) : I→ℤ))≠6 := by
  have hnorm : B (m • (Pi.single i (1:ℤ) : I→ℤ))
      (m • (Pi.single i (1:ℤ) : I→ℤ))=2*m*m := by
    rw [B.smul_left,B.smul_right,hii]
    ring
  rw [hnorm]
  by_cases hsmall : m≤1
  · have hp := mul_nonneg hm (sub_nonneg.mpr hsmall)
    constructor <;> intro he <;> nlinarith
  · have hp := mul_nonneg (by omega : 0≤m-2) (by omega : 0≤m+2)
    constructor <;> intro he <;> nlinarith

theorem exists_positive_off_axis (B : LinearMap.BilinForm ℤ (I→ℤ)) (x : I→ℤ)
    (hx : ∀j,0≤x j) (i : I)
    (hii : B (Pi.single i (1:ℤ) : I→ℤ) (Pi.single i (1:ℤ) : I→ℤ)=2)
    (hnorm : B x x=4 ∨ B x x=6) : ∃j,j≠i ∧ 0<x j := by
  by_contra hn
  have haxis : x=x i • (Pi.single i (1:ℤ) : I→ℤ) := by
    funext j
    by_cases hji : j=i
    · subst j
      simp [Pi.smul_apply]
    · have hz : x j=0 := by
        have hn' : ¬0<x j := fun hp=>hn ⟨j,hji,hp⟩
        have := hx j
        omega
      simp [Pi.smul_apply,hji,hz]
  have hm := norm_four_or_six_not_axis B i hii (x i) (hx i)
  have heq := congrArg (fun v : I→ℤ=>B v v) haxis
  exact hnorm.elim (fun h=>hm.1 (heq.symm.trans h)) (fun h=>hm.2 (heq.symm.trans h))

end SymmetricSubgroupAsymptotics.CFSGIntegerPairingPositiveDescent
