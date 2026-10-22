import SymmetricSubgroupAsymptotics.CFSGLinearFunctionalFibres
import Mathlib.Tactic.Ring

/-! Exact vector count for the literal split odd-dimensional quadratic
equation. Counting affine functional fibres also covers the zero first
coordinate; no orthogonal-group order or transitivity formula is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGParabolicQuadricCount
variable {K I : Type} [Field K] [Fintype I]

def dotDual (x : I → K) : (I → K) →ₗ[K] K where
  toFun y := ∑i,x i*y i
  map_add' y z := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' a y := by
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

def Fibre (x : I → K) := {p : K × (I → K) // dotDual x p.2 + p.1^2=0}

instance fibre_finite [Finite K] (x : I→K) : Finite (Fibre x) :=
  inferInstanceAs (Finite {p : K × (I→K) // dotDual x p.2+p.1^2=0})

def fibreSigmaEquiv (x : I → K) :
    Fibre x ≃ Σz:K,{y:I→K // dotDual x y= -z^2} where
  toFun p := ⟨p.val.1,⟨p.val.2,by
    have h := p.property
    exact eq_neg_iff_add_eq_zero.mpr h⟩⟩
  invFun p := ⟨(p.1,p.2.val),eq_neg_iff_add_eq_zero.mp p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def zeroFibreEquiv : Fibre (0:I→K) ≃ (I→K) where
  toFun p := p.val.2
  invFun y := ⟨(0,y),by simp [dotDual]⟩
  left_inv p := by
    have hp := p.property
    change (∑i:I,(0:K)*p.val.2 i)+p.val.1^2=0 at hp
    have hh : p.val.1^2=0 := by
      simpa only [zero_mul,Finset.sum_const_zero,zero_add] using hp
    have hz : p.val.1=0 := eq_zero_of_pow_eq_zero hh
    exact Subtype.ext (Prod.ext hz.symm rfl)
  right_inv _ := rfl

theorem nonzero_dot_fibre_card [Finite K] (x : I→K) (hx:x≠0) (a:K) :
    Nat.card {y:I→K // dotDual x y=a}=Nat.card K^(Fintype.card I-1) := by
  classical
  obtain ⟨i,hi⟩ : ∃i,x i≠0 := by
    by_contra hn
    apply hx
    funext i
    by_contra hi
    exact hn ⟨i,hi⟩
  let w : I→K := Pi.single i (x i)⁻¹
  have hw : dotDual x w=1 := by
    simp [dotDual,w,Pi.single_apply,mul_ite,hi]
  exact CFSGLinearFunctionalFibres.card_fibre (dotDual x) w hw a

theorem fibre_card [Finite K] (x:I→K) : Nat.card (Fibre x)=Nat.card K^Fintype.card I := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  by_cases hx:x=0
  · subst x
    simpa only [Nat.card_fun,Nat.card_eq_fintype_card (α:=I)] using
      Nat.card_congr (zeroFibreEquiv (K:=K) (I:=I))
  · have hI : 0<Fintype.card I := by
      by_contra hn
      letI : IsEmpty I := Fintype.card_eq_zero_iff.mp (by omega)
      exact hx (funext (fun i=>isEmptyElim i))
    calc
      Nat.card (Fibre x)=Nat.card (Σz:K,{y:I→K //dotDual x y= -z^2}) :=
        Nat.card_congr (fibreSigmaEquiv x)
      _=∑z:K,Nat.card {y:I→K //dotDual x y= -z^2} := Nat.card_sigma
      _=Fintype.card K*Nat.card K^(Fintype.card I-1) := by
        simp only [nonzero_dot_fibre_card x hx,Finset.sum_const,Finset.card_univ,
          nsmul_eq_mul,Nat.cast_id]
      _=Nat.card K^Fintype.card I := by
        rw [←Nat.card_eq_fintype_card,Nat.mul_comm,←pow_succ]
        congr 1
        omega

def Quadric := Σx:I→K,Fibre x

theorem quadric_card [Finite K] : Nat.card (Quadric (K:=K) (I:=I))=
    Nat.card K^(2*Fintype.card I) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  calc
    Nat.card (Quadric (K:=K) (I:=I))=∑x:I→K,Nat.card (Fibre x) := Nat.card_sigma
    _=Fintype.card (I→K)*Nat.card K^Fintype.card I := by
      simp only [fibre_card,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
    _=Nat.card K^Fintype.card I*Nat.card K^Fintype.card I := by
      rw [Fintype.card_fun,←Nat.card_eq_fintype_card (α:=K)]
    _=Nat.card K^(2*Fintype.card I) := by rw [←pow_add,two_mul]

end SymmetricSubgroupAsymptotics.CFSGParabolicQuadricCount
