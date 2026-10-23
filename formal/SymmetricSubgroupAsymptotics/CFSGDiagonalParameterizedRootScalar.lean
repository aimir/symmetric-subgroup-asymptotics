import SymmetricSubgroupAsymptotics.CFSGDiagonalUnitRootAction
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-! A diagonal unit normalizing an actual parameterized matrix root
group acts by one nonzero field scalar whenever one original entry reads
the parameter. The root matrix may be quadratic in its parameter; no
polynomial separation, large-field guard, or linear-root assumption is
needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGDiagonalParameterizedRootScalar
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem diagonal_entry_ne_zero (d : (Matrix I I K)ˣ)
    (hd : (d : Matrix I I K).IsDiag) (i : I) : (d : Matrix I I K) i i≠0 := by
  have hh := congrArg (fun M : Matrix I I K=>M i i) d.val_inv
  have hh' : ((d : Matrix I I K)*(↑(d⁻¹) : Matrix I I K)) i i=1 := by
    simpa only [Matrix.one_apply_eq] using hh
  rw [←hd.diagonal_diag,Matrix.diagonal_mul] at hh'
  exact left_ne_zero_of_mul_eq_one hh'

theorem exists_unit_scalar (u : K→(Matrix I I K)ˣ) (row col : I)
    (hentry : ∀t,(u t : Matrix I I K) row col=t)
    (d : (Matrix I I K)ˣ) (hd : (d : Matrix I I K).IsDiag)
    (hn : ∀t,∃s,d*u t*d⁻¹=u s) :
    ∃c:Kˣ,∀t,d*u t*d⁻¹=u ((c:K)*t) := by
  have hr := diagonal_entry_ne_zero d hd row
  have hc := diagonal_entry_ne_zero d hd col
  let c : Kˣ := Units.mk0 ((d : Matrix I I K) row row/(d : Matrix I I K) col col)
    (div_ne_zero hr hc)
  refine ⟨c,?_⟩
  intro t
  obtain ⟨s,hs⟩ := hn t
  have hm : d*u t=u s*d := by
    calc
      _=(d*u t*d⁻¹)*d := by group
      _=u s*d := by rw [hs]
  have he := congrArg (fun z : (Matrix I I K)ˣ=>(z : Matrix I I K) row col) hm
  change ((d : Matrix I I K)*(u t : Matrix I I K)) row col=
    ((u s : Matrix I I K)*(d : Matrix I I K)) row col at he
  rw [←hd.diagonal_diag,Matrix.diagonal_mul,Matrix.mul_diagonal] at he
  change (d : Matrix I I K) row row*(u t : Matrix I I K) row col=
    (u s : Matrix I I K) row col*(d : Matrix I I K) col col at he
  rw [hentry,hentry] at he
  have hs' : s=(c:K)*t := by
    calc
      s=((d : Matrix I I K) row row*t)/(d : Matrix I I K) col col :=
        (eq_div_iff hc).mpr he.symm
      _=(c:K)*t := by dsimp only [c,Units.val_mk0];ring
  exact hs.trans (congrArg u hs')

end SymmetricSubgroupAsymptotics.CFSGDiagonalParameterizedRootScalar
