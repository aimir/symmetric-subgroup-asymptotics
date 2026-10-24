import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel

/-! Odd orbit averaging extracts a prescribed elementary-two coordinate
from genuine commutator factors. The ambient subgroup and the chosen
orbit images are arbitrary; actual normalization and zero orbit-sum
conditions must be discharged by each application. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOddOrbitCommutatorCoordinates

private theorem sum_sub_const {T V : Type*} [AddCommGroup V]
    (l : List T) (f : T→V) (v : V) :
    (l.map (fun t=>f t-v)).sum=(l.map f).sum-l.length • v := by
  induction l with
  | nil=>simp only [List.map_nil,List.sum_nil,List.length_nil,zero_nsmul,sub_zero]
  | cons a l ih=>
    simp only [List.map_cons,List.sum_cons,List.length_cons,ih,add_nsmul,one_nsmul]
    abel

private theorem odd_nsmul_of_two_zero {V : Type*} [AddCommGroup V]
    (v : V) (hzero : v+v=0) (n : ℕ) (hn : Odd n) : n • v=v := by
  obtain ⟨k,rfl⟩ := hn
  have htwo : (2 : ℕ) • v=0 := by simpa only [two_nsmul] using hzero
  rw [add_nsmul,one_nsmul,mul_nsmul,htwo,nsmul_zero,zero_add]

private theorem coordinate_product {T U V : Type*} [Group U] [AddCommGroup V]
    (phi : U→*Multiplicative V) (l : List T) (c : T→U) (u : U) :
    (phi ((l.map (fun t=>c t*u⁻¹)).prod)).toAdd=
      (l.map (fun t=>(phi (c t)).toAdd-(phi u).toAdd)).sum := by
  induction l with
  | nil=>simp only [List.map_nil,List.prod_nil,map_one,toAdd_one,List.sum_nil]
  | cons a l ih=>
    simp only [List.map_cons,List.prod_cons,map_mul,map_inv,toAdd_mul,toAdd_inv,
      List.sum_cons,ih,sub_eq_add_neg]

theorem commutator_product_coordinate {T U V : Type*} [Group U] [AddCommGroup V]
    (phi : U→*Multiplicative V) (l : List T) (c : T→U) (u : U)
    (htwo : ∀v : V,v+v=0) (hodd : Odd l.length)
    (horbit : (l.map (fun t=>(phi (c t)).toAdd)).sum=0) :
    phi ((l.map (fun t=>c t*u⁻¹)).prod)=phi u := by
  have he : (phi ((l.map (fun t=>c t*u⁻¹)).prod)).toAdd=(phi u).toAdd := by
    rw [coordinate_product,sum_sub_const,horbit,
      odd_nsmul_of_two_zero (phi u).toAdd (htwo _) _ hodd,zero_sub]
    exact neg_eq_of_add_eq_zero_left (htwo _)
  exact congrArg Multiplicative.ofAdd he

theorem exists_mem_same_coordinate {T U V : Type*} [Group U] [AddCommGroup V]
    (S : Subgroup U) (phi : U→*Multiplicative V) (l : List T) (c : T→U) (u : U)
    (htwo : ∀v : V,v+v=0) (hodd : Odd l.length)
    (horbit : (l.map (fun t=>(phi (c t)).toAdd)).sum=0)
    (hcomm : ∀t∈l,c t*u⁻¹∈S) :
    ∃b : U,b∈S ∧ phi b=phi u := by
  refine ⟨(l.map (fun t=>c t*u⁻¹)).prod,?_,
    commutator_product_coordinate phi l c u htwo hodd horbit⟩
  apply S.list_prod_mem
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
  exact hcomm t ht

end SymmetricSubgroupAsymptotics.CFSGOddOrbitCommutatorCoordinates
