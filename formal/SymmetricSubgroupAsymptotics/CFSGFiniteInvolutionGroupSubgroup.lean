import SymmetricSubgroupAsymptotics.CFSGFiniteInvolutionOrbitProduct
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Nodup

/-! Involution-orbit subgroup assembly for arbitrary dependent GROUPS.
An ordered list product suffices: at each coordinate only its own orbit
factor is nonidentity. No commutative-group replacement is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteInvolutionGroupSubgroup
variable {I : Type*} [LinearOrder I] [Fintype I] [d : DecidableEq I]
variable (G : I→Type*) [∀i,Group (G i)] (p : Equiv.Perm I)

private def factor (c : ∀i,G i) (i : I) : ∀j,G j :=
  if p i=i then Pi.mulSingle i (c i)
  else Pi.mulSingle i (c i)*Pi.mulSingle (p i) (c (p i))

private theorem factor_at_representative (hp : Function.Involutive p) (c : ∀i,G i) (j : I) :
    factor G p c (min j (p j)) j=c j := by
  by_cases h : j≤p j
  · rw [min_eq_left h]
    by_cases he : p j=j
    · simp [factor,he]
    · simp [factor,he,Ne.symm he]
  · rw [min_eq_right (le_of_not_ge h)]
    have he : p j≠j := ne_of_lt (lt_of_not_ge h)
    have he' : j≠p j := Ne.symm he
    have hn : p (p j)≠p j := by rw [hp j];exact he'
    rw [factor,if_neg hn]
    change Pi.mulSingle (p j) (c (p j)) j*
      Pi.mulSingle (p (p j)) (c (p (p j))) j=c j
    rw [hp j]
    simp [he']

private theorem factor_other (hp : Function.Involutive p) (c : ∀i,G i) (j i : I)
    (hi : i≤p i) (hne : i≠min j (p j)) : factor G p c i j=1 := by
  have hij : i≠j := by
    intro h
    subst i
    exact hne (min_eq_left hi).symm
  have hpij : p i≠j := by
    intro h
    have he : i=p j := by rw [←h,hp]
    have hj : p j≤j := by rw [he] at hi;rw [hp j] at hi;exact hi
    exact hne (he.trans (min_eq_right hj).symm)
  unfold factor
  split_ifs <;> simp [Ne.symm hij,Ne.symm hpij]

theorem mem_of_singleton_pair_mem (hp : Function.Involutive p)
    (S : Subgroup (∀i,G i)) (c : ∀i,G i)
    (hsingle : ∀i,p i=i → Pi.mulSingle i (c i)∈S)
    (hpair : ∀i,p i≠i → Pi.mulSingle i (c i)*Pi.mulSingle (p i) (c (p i))∈S) : c∈S := by
  let reps : Finset I := Finset.univ.filter (fun i=>i≤p i)
  have hrep (j : I) : min j (p j)∈reps := by
    change min j (p j)∈Finset.univ.filter (fun i=>i≤p i)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases h : j≤p j
    · simpa only [min_eq_left h] using h
    · rw [min_eq_right (le_of_not_ge h),hp]
      exact le_of_not_ge h
  have he : (reps.toList.map (factor G p c)).prod=c := by
    funext j
    rw [Pi.list_prod_apply,List.map_map]
    change (reps.toList.map (fun i=>factor G p c i j)).prod=c j
    rw [List.prod_map_eq_pow_single (min j (p j)) _ (by
      intro i hne hi
      exact factor_other G p hp c j i
        (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2 hne)]
    rw [List.count_eq_one_of_mem reps.nodup_toList (Finset.mem_toList.mpr (hrep j)),pow_one]
    exact factor_at_representative G p hp c j
  rw [←he]
  apply S.list_prod_mem
  intro x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  unfold factor
  split_ifs with hi
  · exact hsingle i hi
  · exact hpair i hi

end SymmetricSubgroupAsymptotics.CFSGFiniteInvolutionGroupSubgroup
