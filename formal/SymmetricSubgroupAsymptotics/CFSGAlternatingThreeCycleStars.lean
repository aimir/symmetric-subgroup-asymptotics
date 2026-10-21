import SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleGeometry

/-! Three compatible 3-cycles determine their common oriented edge.
The tetrahedral support alternative is excluded by the actual product
relations, including in degrees five and six. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleStars
open Equiv Equiv.Perm CFSGAlternatingStarGenerators CFSGAlternatingThreeCycleGeometry
variable {α : Type*} [DecidableEq α]

theorem cycle_support [Fintype α] (a b c : α) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    (cycle a b c).support={a,b,c} := by
  ext x
  simp only [mem_support,cycle,Perm.mul_apply,swap_apply_def,
    Finset.mem_insert,Finset.mem_singleton]
  grind

theorem cycle_isThreeCycle [Fintype α] (a b c : α) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    (cycle a b c).IsThreeCycle := by
  rw [←card_support_eq_three_iff,cycle_support a b c hab hac hbc]
  simp [hab,hac,hbc]

private theorem incompatible_second_edge (a b c d e : α)
    (hfour : [a,b,c,d].Nodup) (hea : e≠a) (heb : e≠b) (hec : e≠c) :
    (cycle a b d*cycle b c e)^2≠1 := by
  intro h
  have hx := congrArg (fun p : Perm α => p c) h
  simp only [pow_two,cycle,Perm.mul_apply,Perm.one_apply,swap_apply_def] at hx
  grind

private theorem incompatible_third_edge (a b c d e : α)
    (hfour : [a,b,c,d].Nodup) (_hea : e≠a) (heb : e≠b) (hec : e≠c) :
    (cycle a b d*cycle c a e)^2≠1 := by
  intro h
  have hx := congrArg (fun p : Perm α => p c) h
  simp only [pow_two,cycle,Perm.mul_apply,Perm.one_apply,swap_apply_def] at hx
  grind

/-- Once two compatible cycles have been put in star form, every third
compatible cycle lies on their same ordered pair, with a new point. -/
theorem third_normal_form [Fintype α] (a b c d : α) (hfour : [a,b,c,d].Nodup)
    (r : Perm α) (hr : r.IsThreeCycle)
    (hpr : (cycle a b c*r)^2=1) (hne : cycle a b c*r≠1)
    (hqr : (cycle a b d*r)^2=1) :
    ∃ e : α,[a,b,c,d,e].Nodup ∧ r=cycle a b e := by
  obtain ⟨x,y,z,e,hxyze,hp,hr'⟩ := pair_normal_form (cycle a b c) r
    (cycle_isThreeCycle a b c (by grind) (by grind) (by grind)) hr hpr hne
  have hx : x∈(cycle a b c).support := by
    rw [hp,cycle_support x y z (by grind) (by grind) (by grind)]
    simp
  rw [cycle_support a b c (by grind) (by grind) (by grind)] at hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  have hxy : (cycle a b c) x=y := by
    rw [hp]
    simp only [cycle,Perm.mul_apply,swap_apply_def]
    grind
  rcases hx with hxa | hxb | hxc
  · subst x
    have hy : y=b := by
      simp only [cycle,Perm.mul_apply,swap_apply_def] at hxy
      grind
    rw [hy] at hr' hxyze hp
    have hec : e≠c := by
      intro he
      subst e
      rw [hr'] at hpr
      have ht := congrArg (fun p : Perm α => p a) hpr
      simp only [pow_two,cycle,Perm.mul_apply,Perm.one_apply,swap_apply_def] at ht
      grind
    have hed : e≠d := by
      intro he
      subst e
      rw [hr'] at hqr
      have ht := congrArg (fun p : Perm α => p a) hqr
      simp only [pow_two,cycle,Perm.mul_apply,Perm.one_apply,swap_apply_def] at ht
      grind
    exact ⟨e,by grind,hr'⟩
  · subst x
    have hy : y=c := by
      simp only [cycle,Perm.mul_apply,swap_apply_def] at hxy
      grind
    rw [hy] at hr' hxyze hp
    have hea : e≠a := by
      intro he
      subst e
      have hz : z=a := by
        have hz' := congrArg (fun p : Perm α => p c) hp
        simp only [cycle,Perm.mul_apply,swap_apply_def] at hz'
        grind
      subst z
      grind
    exact False.elim (incompatible_second_edge a b c d e hfour hea (by grind) (by grind)
      (by simpa only [hr'] using hqr))
  · subst x
    have hy : y=a := by
      simp only [cycle,Perm.mul_apply,swap_apply_def] at hxy
      grind
    rw [hy] at hr' hxyze hp
    have heb : e≠b := by
      intro he
      subst e
      have hz : z=b := by
        have hz' := congrArg (fun p : Perm α => p a) hp
        simp only [cycle,Perm.mul_apply,swap_apply_def] at hz'
        grind
      subst z
      grind
    exact False.elim (incompatible_third_edge a b c d e hfour (by grind) heb (by grind)
      (by simpa only [hr'] using hqr))

end SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCycleStars
