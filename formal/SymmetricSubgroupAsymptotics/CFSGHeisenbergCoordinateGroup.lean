import Mathlib.LinearAlgebra.StdBasis
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-! Literal Heisenberg coordinates over a commutative ring. The central
coordinate and vector quotient are actual homomorphisms. This model is
used with prime-field coefficients inside the original exceptional root
group; no splitting or recognition statement is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergCoordinateGroup

@[ext] structure Element (K : Type*) (m : ℕ) where
  a : Fin m→K
  b : Fin m→K
  c : K
  deriving DecidableEq

variable {K : Type*} [CommRing K] {m : ℕ}

def dot (b a:Fin m→K) : K := ∑i,b i*a i

private theorem dot_zero_left (a:Fin m→K) : dot 0 a=0 := by simp [dot]
private theorem dot_zero_right (b:Fin m→K) : dot b 0=0 := by simp [dot]
private theorem dot_add_left (a b c:Fin m→K) : dot (a+b) c=dot a c+dot b c := by
  simp [dot,add_mul,Finset.sum_add_distrib]
private theorem dot_add_right (a b c:Fin m→K) : dot a (b+c)=dot a b+dot a c := by
  simp [dot,mul_add,Finset.sum_add_distrib]
private theorem dot_neg_left (a b:Fin m→K) : dot (-a) b= -dot a b := by
  simp [dot,Finset.sum_neg_distrib]
private theorem dot_neg_right (a b:Fin m→K) : dot a (-b)= -dot a b := by
  simp [dot,Finset.sum_neg_distrib]

instance : Mul (Element K m) := ⟨fun g h=>⟨g.a+h.a,g.b+h.b,g.c+h.c+dot g.b h.a⟩⟩
instance : One (Element K m) := ⟨⟨0,0,0⟩⟩
instance : Inv (Element K m) := ⟨fun g=>⟨-g.a,-g.b,-g.c+dot g.b g.a⟩⟩

instance : Group (Element K m) where
  mul_assoc g h k := by
    apply Element.ext
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
    · change (g.c+h.c+dot g.b h.a)+k.c+dot (g.b+h.b) k.a=
        g.c+(h.c+k.c+dot h.b k.a)+dot g.b (h.a+k.a)
      rw [dot_add_left,dot_add_right]
      ring
  one_mul g := by
    apply Element.ext
    · exact zero_add _
    · exact zero_add _
    · change 0+g.c+dot 0 g.a=g.c
      rw [zero_add,dot_zero_left,add_zero]
  mul_one g := by
    apply Element.ext
    · exact add_zero _
    · exact add_zero _
    · change g.c+0+dot g.b 0=g.c
      rw [add_zero,dot_zero_right,add_zero]
  inv_mul_cancel g := by
    apply Element.ext
    · exact neg_add_cancel _
    · exact neg_add_cancel _
    · change (-g.c+dot g.b g.a)+g.c+dot (-g.b) g.a=0
      rw [dot_neg_left]
      ring

def coordinates : Element K m≃(Fin m→K)×(Fin m→K)×K where
  toFun g := (g.a,g.b,g.c)
  invFun v := ⟨v.1,v.2.1,v.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite K] : Finite (Element K m) := Finite.of_equiv _ coordinates.symm

def projection : Element K m→*Multiplicative ((Fin m→K)×(Fin m→K)) where
  toFun g := Multiplicative.ofAdd (g.a,g.b)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projection_surjective : Function.Surjective (projection (K:=K) (m:=m)) := by
  intro v
  exact ⟨⟨v.toAdd.1,v.toAdd.2,0⟩,rfl⟩

def central : Multiplicative K→*Element K m where
  toFun z := ⟨0,0,z.toAdd⟩
  map_one' := rfl
  map_mul' z w := by
    apply Element.ext
    · exact (zero_add _).symm
    · exact (zero_add _).symm
    · change z.toAdd+w.toAdd=z.toAdd+w.toAdd+dot 0 0
      rw [dot_zero_left,add_zero]

theorem central_injective : Function.Injective (central (K:=K) (m:=m)) := by
  intro z w he
  exact Multiplicative.toAdd.injective (congrArg Element.c he)

theorem mem_projection_ker (g:Element K m) :
    g∈(projection (K:=K) (m:=m)).ker ↔ g.a=0 ∧ g.b=0 := by
  change (g.a,g.b)=(0,0) ↔ _
  simp only [Prod.mk.injEq]

def kernelChart : Multiplicative K≃*(projection (K:=K) (m:=m)).ker where
  toFun z := ⟨central z,by change ((0:Fin m→K),0)=(0,0);rfl⟩
  invFun g := Multiplicative.ofAdd g.val.c
  left_inv _ := rfl
  right_inv g := by
    obtain ⟨ha,hb⟩ := (mem_projection_ker g.val).mp g.property
    apply Subtype.ext
    change (⟨0,0,g.val.c⟩:Element K m)=g.val
    exact Element.ext ha.symm hb.symm rfl
  map_mul' z w := Subtype.ext (central.map_mul z w)

theorem projection_ker_central :
    (projection (K:=K) (m:=m)).ker≤Subgroup.center (Element K m) := by
  intro g hg
  obtain ⟨ha,hb⟩ := (mem_projection_ker g).mp hg
  rw [Subgroup.mem_center_iff]
  intro h
  apply Element.ext
  · change h.a+g.a=g.a+h.a
    rw [ha,add_zero,zero_add]
  · change h.b+g.b=g.b+h.b
    rw [hb,add_zero,zero_add]
  · change h.c+g.c+dot h.b g.a=g.c+h.c+dot g.b h.a
    rw [ha,hb,dot_zero_left,dot_zero_right,add_zero,add_zero,add_comm h.c g.c]

theorem commutator (g h:Element K m) :
    g*h*g⁻¹*h⁻¹=central (Multiplicative.ofAdd (dot g.b h.a-dot h.b g.a)) := by
  apply Element.ext
  · change ((g.a+h.a)+ -g.a)+ -h.a=0
    abel
  · change ((g.b+h.b)+ -g.b)+ -h.b=0
    abel
  · change ((g.c+h.c+dot g.b h.a)+(-g.c+dot g.b g.a)+dot (g.b+h.b) (-g.a))+
      (-h.c+dot h.b h.a)+dot ((g.b+h.b)+ -g.b) (-h.a)=dot g.b h.a-dot h.b g.a
    simp only [dot_add_left,dot_neg_right,dot_neg_left]
    ring

theorem card [Finite K] : Nat.card (Element K m)=Nat.card K^(2*m+1) := by
  rw [Nat.card_congr (coordinates (K:=K) (m:=m)),Nat.card_prod,Nat.card_prod,
    Nat.card_fun,Nat.card_fin]
  rw [←pow_succ,←pow_add]
  congr 1
  omega

theorem kernel_card [Finite K] : Nat.card (projection (K:=K) (m:=m)).ker=Nat.card K :=
  (Nat.card_congr (kernelChart (K:=K) (m:=m)).toEquiv).symm.trans
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative K≃K))

end SymmetricSubgroupAsymptotics.CFSGHeisenbergCoordinateGroup
