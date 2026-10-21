import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! Symbolic star generators for the alternating group. These identities
use actual point permutations and do not enumerate a symmetric group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingStarGenerators
open Equiv Equiv.Perm
variable {α : Type*} [DecidableEq α]

/-- The oriented cycle `a → b → c → a` when the three points differ. -/
def cycle (a b c : α) : Perm α := swap a b * swap b c

theorem cycle_rotate (a b c : α) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    cycle a b c=cycle b c a := by
  ext x
  simp only [cycle,Perm.mul_apply,swap_apply_def]
  grind

theorem cycle_inverse (a b c : α) : (cycle a b c)⁻¹=cycle c b a := by
  simp only [cycle,mul_inv_rev,swap_inv,swap_comm]

theorem star_difference (a b c d : α)
    (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    cycle a b d*(cycle a b c)⁻¹=cycle a c d := by
  ext x
  simp only [cycle,mul_inv_rev,swap_inv,Perm.mul_apply,swap_apply_def]
  grind

theorem anchored_product (a b c d : α)
    (hab : a≠b) (hac : a≠c) (_had : a≠d)
    (hbc : b≠c) (_hbd : b≠d) (_hcd : c≠d) :
    cycle a b c*cycle a c d=cycle b c d := by
  ext x
  simp only [cycle,Perm.mul_apply,swap_apply_def]
  grind

/-- A subgroup containing all oriented cycles on one fixed pair contains
all cycles on three distinct points. -/
theorem cycle_mem_of_star (H : Subgroup (Perm α)) (a b : α) (hab : a≠b)
    (hstar : ∀ c,c≠a→c≠b→cycle a b c∈H)
    (i j k : α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    cycle i j k∈H := by
  have anchor : ∀ x y,x≠a→y≠a→x≠y→cycle a x y∈H := by
    intro x y hxa hya hxy
    by_cases hxb : x=b
    · subst x
      exact hstar y hya (Ne.symm hxy)
    by_cases hyb : y=b
    · subst y
      have hi := H.inv_mem (hstar x hxa hxb)
      rw [cycle_inverse,cycle_rotate x b a hxb hxa (Ne.symm hab),
        cycle_rotate b a x (Ne.symm hab) (Ne.symm hxb) (Ne.symm hxa)] at hi
      exact hi
    rw [←star_difference a b x y hab (Ne.symm hxa) (Ne.symm hya) (Ne.symm hxb) (Ne.symm hyb) hxy]
    exact H.mul_mem (hstar y hya hyb) (H.inv_mem (hstar x hxa hxb))
  by_cases hia : i=a
  · subst i
    exact anchor j k (Ne.symm hij) (Ne.symm hik) hjk
  by_cases hja : j=a
  · subst j
    rw [cycle_rotate i a k hij hik hjk]
    exact anchor k i (Ne.symm hjk) hij (Ne.symm hik)
  by_cases hka : k=a
  · subst k
    rw [cycle_rotate i j a hij hik hjk,cycle_rotate j a i hjk (Ne.symm hij) (Ne.symm hik)]
    exact anchor i j hik hjk hij
  rw [←anchored_product a i j k (Ne.symm hia) (Ne.symm hja) (Ne.symm hka) hij hik hjk]
  exact H.mul_mem (anchor i j hia hja hij) (anchor j k hja hka hjk)

variable [Fintype α]

/-- The oriented cycles on a fixed pair generate the entire alternating
subgroup. Only two distinguished points are required; all remaining
points keep their original labels. -/
theorem alternating_le_of_star (H : Subgroup (Perm α)) (a b : α) (hab : a≠b)
    (hstar : ∀ c,c≠a→c≠b→cycle a b c∈H) : alternatingGroup α≤H := by
  rw [←Equiv.Perm.closure_three_cycles_eq_alternating]
  apply (Subgroup.closure_le H).mpr
  intro g hg
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by rw [hg.card_support];omega)
  have hnodup := hg.nodup_iff_mem_support.mpr hx
  have he := hg.eq_swap_mul_swap_iff_mem_support.mpr hx
  rw [he]
  exact cycle_mem_of_star H a b hab hstar x (g x) (g (g x))
    (by grind) (by grind) (by grind)

end SymmetricSubgroupAsymptotics.CFSGAlternatingStarGenerators
