import SymmetricSubgroupAsymptotics.CFSGHeisenbergCoordinateGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.FieldSimp

/-! The vector quotient and literal centre of the coordinate Heisenberg
group. The commutator is a nondegenerate alternating bilinear form in
every characteristic, including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergSymplecticQuotient
open CFSGHeisenbergCoordinateGroup
variable {K : Type*} [Field K] {m : ℕ}

private theorem dot_add_left (a b c:Fin m→K) : dot (a+b) c=dot a c+dot b c := by
  simp [dot,add_mul,Finset.sum_add_distrib]
private theorem dot_add_right (a b c:Fin m→K) : dot a (b+c)=dot a b+dot a c := by
  simp [dot,mul_add,Finset.sum_add_distrib]
private theorem dot_smul_left (a b:Fin m→K) (t:K) : dot (t • a) b=t*dot a b := by
  simp [dot,mul_assoc,Finset.mul_sum]
private theorem dot_smul_right (a b:Fin m→K) (t:K) : dot a (t • b)=t*dot a b := by
  simp only [dot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def pairing : LinearMap.BilinForm K ((Fin m→K)×(Fin m→K)) where
  toFun v :=
    { toFun := fun w=>dot v.2 w.1-dot w.2 v.1
      map_add' := by
        intro u w
        change dot v.2 (u.1+w.1)-dot (u.2+w.2) v.1=
          (dot v.2 u.1-dot u.2 v.1)+(dot v.2 w.1-dot w.2 v.1)
        rw [dot_add_right,dot_add_left]
        ring
      map_smul' := by
        intro t w
        change dot v.2 (t • w.1)-dot (t • w.2) v.1=t*(dot v.2 w.1-dot w.2 v.1)
        rw [dot_smul_right,dot_smul_left]
        ring }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change dot (u.2+v.2) w.1-dot w.2 (u.1+v.1)=
      (dot u.2 w.1-dot w.2 u.1)+(dot v.2 w.1-dot w.2 v.1)
    rw [dot_add_left,dot_add_right]
    ring
  map_smul' := by
    intro t v
    apply LinearMap.ext
    intro w
    change dot (t • v.2) w.1-dot w.2 (t • v.1)=t*(dot v.2 w.1-dot w.2 v.1)
    rw [dot_smul_left,dot_smul_right]
    ring

theorem pairing_apply (v w:(Fin m→K)×(Fin m→K)) : pairing v w=dot v.2 w.1-dot w.2 v.1 := rfl

theorem pairing_alt (v:(Fin m→K)×(Fin m→K)) : pairing v v=0 := sub_self _

private theorem dot_single_right (a:Fin m→K)(i:Fin m)(t:K) : dot a (Pi.single i t)=a i*t := by
  simp [dot,Pi.single_apply,mul_ite]
private theorem dot_single_left (a:Fin m→K)(i:Fin m)(t:K) : dot (Pi.single i t) a=t*a i := by
  simp [dot,Pi.single_apply,ite_mul]

theorem pairing_full (v:(Fin m→K)×(Fin m→K)) (hv:v≠0) : Function.Surjective (pairing v) := by
  intro z
  by_cases hb:v.2=0
  · have ha:v.1≠0 := by
      intro ha
      exact hv (Prod.ext ha hb)
    obtain ⟨i,hi⟩ := Function.ne_iff.mp ha
    change v.1 i≠0 at hi
    refine ⟨(0,Pi.single i (-z/(v.1 i))),?_⟩
    change dot v.2 0-dot (Pi.single i (-z/(v.1 i))) v.1=z
    rw [dot_single_left]
    simp only [dot,Pi.zero_apply,mul_zero,Finset.sum_const_zero,zero_sub]
    field_simp [hi] <;> ring
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp hb
    change v.2 i≠0 at hi
    refine ⟨(Pi.single i (z/(v.2 i)),0),?_⟩
    change dot v.2 (Pi.single i (z/(v.2 i)))-dot 0 v.1=z
    rw [dot_single_right]
    simp only [dot,Pi.zero_apply,zero_mul,Finset.sum_const_zero,sub_zero]
    field_simp [hi] <;> ring

theorem commutator_eq_pairing (g h:Element K m) :
    g*h*g⁻¹*h⁻¹=central (Multiplicative.ofAdd (pairing (g.a,g.b) (h.a,h.b))) :=
  commutator g h

theorem central_range_eq_kernel :
    (central (K:=K) (m:=m)).range=(projection (K:=K) (m:=m)).ker := by
  ext g
  constructor
  · rintro ⟨z,rfl⟩
    change ((0:Fin m→K),0)=(0,0)
    rfl
  · intro hg
    refine ⟨(kernelChart (K:=K) (m:=m)).symm ⟨g,hg⟩,?_⟩
    exact congrArg Subtype.val ((kernelChart (K:=K) (m:=m)).apply_symm_apply ⟨g,hg⟩)

theorem center_eq_kernel :
    Subgroup.center (Element K m)=(projection (K:=K) (m:=m)).ker := by
  apply le_antisymm _ projection_ker_central
  intro g hg
  have hzero (w:(Fin m→K)×(Fin m→K)) : pairing (g.a,g.b) w=0 := by
    let h:Element K m := ⟨w.1,w.2,0⟩
    have hc:Commute g h := (Subgroup.mem_center_iff.mp hg h).symm
    have he : g*h*g⁻¹*h⁻¹=1 := commutatorElement_eq_one_iff_commute.mpr hc
    rw [commutator_eq_pairing] at he
    have he' : Multiplicative.ofAdd (pairing (g.a,g.b) w)=1 :=
      central_injective (he.trans (map_one central).symm)
    exact congrArg Multiplicative.toAdd he'
  have hv : (g.a,g.b)=(0,0) := by
    by_contra hv
    obtain ⟨w,hw⟩ := pairing_full (g.a,g.b) hv 1
    exact one_ne_zero (hw.symm.trans (hzero w))
  exact (mem_projection_ker g).mpr (Prod.mk.inj hv)

def centerChart : Multiplicative K≃*Subgroup.center (Element K m) :=
  (kernelChart (K:=K) (m:=m)).trans (MulEquiv.subgroupCongr center_eq_kernel.symm)

theorem center_card [Finite K] : Nat.card (Subgroup.center (Element K m))=Nat.card K :=
  (Nat.card_congr (centerChart (K:=K) (m:=m)).toEquiv).symm.trans
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative K≃K))

end SymmetricSubgroupAsymptotics.CFSGHeisenbergSymplecticQuotient
