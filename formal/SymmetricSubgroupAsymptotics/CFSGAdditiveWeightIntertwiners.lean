import SymmetricSubgroupAsymptotics.CFSGCharacteristicThreeWeightRigidity
import Mathlib.Tactic.FinCases

/-! A nonzero additive weight intertwiner can be normalized at any
nonzero image. The characteristic-three identities then rule out the
two nonlinear weights whenever the pinned endomorphism moves a point. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAdditiveWeightIntertwiners

def normalizedAt {K : Type*} [Field K] (h : K→+K) (a : K) : K→+K where
  toFun x := h (a*x)/h a
  map_zero' := by rw [mul_zero,map_zero,zero_div]
  map_add' x y := by rw [mul_add,map_add,add_div]

theorem normalizedAt_one {K : Type*} [Field K] (h : K→+K) (a : K) (ha : h a≠0) :
    normalizedAt h a 1=1 := by
  change h (a*1)/h a=1
  rw [mul_one,div_self ha]

theorem middle_square_intertwiner_eq_zero {K : Type*} [Field K] [CharP K 3]
    (α : K→+*K) (hmoved : ∃x,α x≠x) (h : K→+K)
    (hscale : ∀a x,h (a*x^2)=h a*(x*α x)^2) : h=0 := by
  obtain ⟨x,hx⟩ := hmoved
  apply AddMonoidHom.ext
  intro a
  change h a=0
  by_contra ha
  have hs (b : K) : normalizedAt h a (b^2)=(b*α b)^2 := by
    change h (a*b^2)/h a=(b*α b)^2
    rw [hscale]
    field_simp [ha]
  exact hx (CFSGCharacteristicThreeWeightRigidity.middle_square_rigidity
    α (normalizedAt h a) (normalizedAt_one h a ha) hs x)

theorem cube_square_intertwiner_eq_zero {K : Type*} [Field K] [Finite K] [CharP K 3]
    (hcard : Nat.card K%4=3) (α : K→+*K) (hmoved : ∃x,α x≠x) (h : K→+K)
    (hscale : ∀a x,h (a*x^2)=h a*((x^2)^2*α (x^2))) : h=0 := by
  obtain ⟨x,hx⟩ := hmoved
  apply AddMonoidHom.ext
  intro a
  change h a=0
  by_contra ha
  have hs (b : K) : normalizedAt h a (b^2)=(b^2)^2*α (b^2) := by
    change h (a*b^2)/h a=(b^2)^2*α (b^2)
    rw [hscale]
    field_simp [ha]
  exact hx (CFSGCharacteristicThreeWeightRigidity.cube_square_rigidity
    hcard α (normalizedAt h a) (normalizedAt_one h a ha) hs x)

theorem exists_moved_of_cube {K : Type*} [Field K] [Finite K]
    (α : K→+*K) (hα : ∀x,α (α x)=x^3) (hcard : 3<Nat.card K) : ∃x,α x≠x := by
  classical
  by_contra hn
  have hfix (x : K) : α x=x := Classical.byContradiction (fun hx=>hn ⟨x,hx⟩)
  have hthree (x : K) : x=0 ∨ x=1 ∨ x=-1 := by
    have hx : x^3=x := by simpa only [hfix] using (hα x).symm
    have hz : x*(x-1)*(x+1)=0 := by
      calc
        _ = x^3-x := by ring
        _ = 0 := sub_eq_zero.mpr hx
    rcases mul_eq_zero.mp hz with hz | hz
    · rcases mul_eq_zero.mp hz with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Or.inl (sub_eq_zero.mp h1))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left hz))
  have hs : Function.Surjective (fun i:Fin 3=>(![0,1,-1]:Fin 3→K) i) := by
    intro x
    rcases hthree x with hx | hx | hx
    · exact ⟨0,hx.symm⟩
    · exact ⟨1,hx.symm⟩
    · exact ⟨2,hx.symm⟩
  have hc := Nat.card_le_card_of_surjective _ hs
  rw [Nat.card_fin] at hc
  exact (not_le_of_gt hcard) hc

end SymmetricSubgroupAsymptotics.CFSGAdditiveWeightIntertwiners
