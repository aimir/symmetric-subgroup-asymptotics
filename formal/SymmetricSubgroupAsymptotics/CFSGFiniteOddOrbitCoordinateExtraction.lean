import SymmetricSubgroupAsymptotics.CFSGOddOrbitCommutatorCoordinates
import Mathlib.Algebra.BigOperators.Fin

/-! The finite-type form of odd orbit coordinate extraction. Enumeration
is used only to form an ordered product in a possibly noncommutative
group; all sums retain the exact finite orbit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFiniteOddOrbitCoordinateExtraction
open CFSGOddOrbitCommutatorCoordinates

theorem exists_mem_same_coordinate {T U V : Type*} [Fintype T] [Group U] [AddCommGroup V]
    (S : Subgroup U) (phi : U→*Multiplicative V) (c : T→U) (u : U)
    (htwo : ∀v : V,v+v=0) (hodd : Odd (Fintype.card T))
    (horbit : ∑t : T,(phi (c t)).toAdd=0)
    (hcomm : ∀t : T,c t*u⁻¹∈S) :
    ∃b : U,b∈S ∧ phi b=phi u := by
  let e : Fin (Fintype.card T)≃T := (Fintype.equivFin T).symm
  let l : List T := List.ofFn e
  have hl : Odd l.length := by simpa only [l,List.length_ofFn] using hodd
  have hs : (l.map (fun t=>(phi (c t)).toAdd)).sum=0 := by
    dsimp only [l]
    rw [List.map_ofFn,List.sum_ofFn]
    exact (Equiv.sum_comp e (fun t : T=>(phi (c t)).toAdd)).trans horbit
  exact CFSGOddOrbitCommutatorCoordinates.exists_mem_same_coordinate S phi l c u htwo hl hs
    (fun t _=>hcomm t)

end SymmetricSubgroupAsymptotics.CFSGFiniteOddOrbitCoordinateExtraction
