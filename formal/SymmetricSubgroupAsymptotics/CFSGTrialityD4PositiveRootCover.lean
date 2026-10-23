import SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootOrbits
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exhaustiveness of the displayed positive D4 triality root orbits.
A proved integer energy identity bounds the four coordinates; only the
24 bounded coordinate cases are then checked. No exporter or assumed
root census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootCover
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGTrialityD4PositiveRootOrbits

theorem energy_formula (x : Fin 4→ℤ) :
    (2*x 0-x 1)^2+(2*x 2-x 1)^2+(2*x 3-x 1)^2+(x 1)^2=
      2*integerPairing (CartanMatrix.D 4) x x := by
  have hlast : Fin.succ (2 : Fin 3) = (3 : Fin 4) := rfl
  norm_num [integerPairing,Matrix.toBilin'_apply,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,cartan_eq,hlast] <;> ring

theorem positive_coordinate_bounds (x : Roots (CartanMatrix.D 4))
    (hx : ∀ i,0≤x.val i) :
    x.val 0≤1 ∧ x.val 1≤2 ∧ x.val 2≤1 ∧ x.val 3≤1 := by
  have he:=energy_formula x.val
  rw [x.property] at he
  have hb2 : (x.val 1)^2≤4 := by
    nlinarith [sq_nonneg (2*x.val 0-x.val 1),sq_nonneg (2*x.val 2-x.val 1),
      sq_nonneg (2*x.val 3-x.val 1)]
  have ha2 : (x.val 0)^2≤2 := by
    nlinarith [sq_nonneg (x.val 0-x.val 1),sq_nonneg (2*x.val 2-x.val 1),
      sq_nonneg (2*x.val 3-x.val 1)]
  have hc2 : (x.val 2)^2≤2 := by
    nlinarith [sq_nonneg (x.val 2-x.val 1),sq_nonneg (2*x.val 0-x.val 1),
      sq_nonneg (2*x.val 3-x.val 1)]
  have hd2 : (x.val 3)^2≤2 := by
    nlinarith [sq_nonneg (x.val 3-x.val 1),sq_nonneg (2*x.val 0-x.val 1),
      sq_nonneg (2*x.val 2-x.val 1)]
  have ha : x.val 0≤1 := by
    by_contra hn
    have h2 : 2≤x.val 0:=by omega
    nlinarith [sq_nonneg (x.val 0-1)]
  have hb : x.val 1≤2 := by
    by_contra hn
    have h3 : 3≤x.val 1:=by omega
    nlinarith [sq_nonneg (x.val 1-2)]
  have hc : x.val 2≤1 := by
    by_contra hn
    have h2 : 2≤x.val 2:=by omega
    nlinarith [sq_nonneg (x.val 2-1)]
  have hd : x.val 3≤1 := by
    by_contra hn
    have h2 : 2≤x.val 3:=by omega
    nlinarith [sq_nonneg (x.val 3-1)]
  exact ⟨ha,hb,hc,hd⟩

theorem bounded_coordinates_cover (a b c d : ℤ)
    (ha0 : 0≤a) (ha1 : a≤1) (hb0 : 0≤b) (hb2 : b≤2)
    (hc0 : 0≤c) (hc1 : c≤1) (hd0 : 0≤d) (hd1 : d≤1)
    (he : (2*a-b)^2+(2*c-b)^2+(2*d-b)^2+b^2=4) :
    (∃ s k : Fin 3, ![a,b,c,d]=shortCoordinates s k) ∨
      ∃ s : Fin 3, ![a,b,c,d]=longCoordinates s := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    norm_num at he <;> decide

theorem positive_root_cover (x : Roots (CartanMatrix.D 4)) (hx : ∀ i,0≤x.val i) :
    (∃ s k : Fin 3,x=shortRoot s k) ∨ ∃ s : Fin 3,x=longRoot s := by
  obtain ⟨ha,hb,hc,hd⟩:=positive_coordinate_bounds x hx
  have he:=energy_formula x.val
  rw [x.property] at he
  norm_num at he
  have hv : x.val=![x.val 0,x.val 1,x.val 2,x.val 3] := by
    funext i
    fin_cases i <;> rfl
  rcases bounded_coordinates_cover (x.val 0) (x.val 1) (x.val 2) (x.val 3)
      (hx 0) ha (hx 1) hb (hx 2) hc (hx 3) hd he with ⟨s,k,h⟩|⟨s,h⟩
  · exact Or.inl ⟨s,k,Subtype.ext (hv.trans h)⟩
  · exact Or.inr ⟨s,Subtype.ext (hv.trans h)⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootCover
