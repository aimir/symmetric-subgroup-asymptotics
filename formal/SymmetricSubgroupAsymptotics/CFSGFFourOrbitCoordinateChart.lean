import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Basic

/-! Disjoint singleton/paired orbit factors have independent actual
group coordinates. Products are ordered LIST products, so no abelian
instance is imposed on the groups. Evaluation at each chosen orbit
representative recovers its input, independently of the ordering. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOrbitCoordinateChart
variable {I J : Type*} [DecidableEq I] [DecidableEq J]
    (G : I→Type*) [∀i,Group (G i)] (p : Equiv.Perm I)
    (T : ∀i,G i→*G (p i)) (r : J→I)

def orbitCoordinate (j : J) (x : G (r j)) : ∀i,G i :=
  if p (r j)=r j then Pi.mulSingle (r j) x else
    Pi.mulSingle (r j) x*Pi.mulSingle (p (r j)) (T (r j) x)

theorem orbitCoordinate_self (j : J) (x : G (r j)) :
    orbitCoordinate G p T r j x (r j)=x := by
  unfold orbitCoordinate
  split_ifs with hp
  · simp
  · simp [hp]

variable (hdisj : ∀j k,r j=r k ∨ r j=p (r k)→j=k)

include hdisj in
theorem orbitCoordinate_other (j k : J) (hjk : j≠k) (x : G (r j)) :
    orbitCoordinate G p T r j x (r k)=1 := by
  have hr : r j≠r k := fun he=>hjk (hdisj j k (Or.inl he))
  have hp : p (r j)≠r k := fun he=>hjk (hdisj k j (Or.inr he.symm)).symm
  unfold orbitCoordinate
  split_ifs <;> simp [hr,hp]

variable [Fintype J]

def orbitChart (c : ∀j,G (r j)) : ∀i,G i :=
  ((Finset.univ : Finset J).toList.map (fun j=>orbitCoordinate G p T r j (c j))).prod

include hdisj in
theorem orbitChart_eval (c : ∀j,G (r j)) (k : J) :
    orbitChart G p T r c (r k)=c k := by
  let l := (Finset.univ : Finset J).toList
  let F : J→G (r k) := fun j=>orbitCoordinate G p T r j (c j) (r k)
  have hmap : orbitChart G p T r c (r k)=(l.map F).prod := by
    have he := (Pi.evalMonoidHom G (r k)).map_list_prod
      (l.map (fun j=>orbitCoordinate G p T r j (c j)))
    simpa only [orbitChart,l,List.map_map,Function.comp_apply,Pi.coe_evalMonoidHom] using he
  rw [hmap,List.prod_map_eq_pow_single k F (fun j hj _=>
    orbitCoordinate_other G p T r hdisj j k hj (c j))]
  have hcount : l.count k=1 := List.count_eq_one_of_mem (Finset.nodup_toList _)
    (by simp [l])
  rw [hcount,pow_one]
  exact orbitCoordinate_self G p T r k (c k)

include hdisj in
theorem orbitChart_injective : Function.Injective (orbitChart G p T r) := by
  intro c d he
  funext k
  have hk := congrFun he (r k)
  rw [orbitChart_eval G p T r hdisj,orbitChart_eval G p T r hdisj] at hk
  exact hk

end SymmetricSubgroupAsymptotics.CFSGFFourOrbitCoordinateChart
