import SymmetricSubgroupAsymptotics.CFSGYArmProductGeneration
import SymmetricSubgroupAsymptotics.InvolutionChainShortPeriods

/-! Genuine arm periods and cross-arm commutation in the ORIGINAL Y
presentation. These bind the exact generic word identities to the named
arm products; no period or finite-model assertion is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYArmProductPeriods
open CFSG.Models.YGroups CFSGGeneration CFSGReduction CFSGYArmProductGeneration

private def entry (arms : Arms) (i : Fin 3) {k : ℕ} (h : arms.length i = k)
    (d : Fin k) : CFSG.Models.YGroups.Group arms :=
  PresentedGroup.of (rels := relations arms) (some ⟨i,Fin.cast h.symm d⟩)

private theorem product_eq (arms : Arms) (i : Fin 3) (k : ℕ) (h : arms.length i = k) :
    armProduct arms i = (List.ofFn (entry arms i h)).prod := by
  exact congrArg List.prod (List.ofFn_congr h
    (fun d : Fin (arms.length i) => PresentedGroup.of (rels := relations arms) (some ⟨i,d⟩)))

private theorem entry_square (arms : Arms) (i : Fin 3) {k : ℕ} (h : arms.length i = k)
    (d : Fin k) : (entry arms i h d)^2 = 1 :=
  y_generator_sq arms (some ⟨i,Fin.cast h.symm d⟩)

private theorem entry_adjacent (arms : Arms) (i : Fin 3) {k : ℕ} (h : arms.length i = k)
    (d e : Fin k) (hde : d.val+1 = e.val) :
    (entry arms i h d*entry arms i h e)^3 = 1 :=
  y_adjacent_product_cube arms (some ⟨i,Fin.cast h.symm d⟩)
    (some ⟨i,Fin.cast h.symm e⟩) ⟨rfl,Or.inl hde⟩

private theorem nonadjacent_commute (arms : Arms) (u v : Node arms)
    (h : yNonadjacent arms u v) :
    Commute (PresentedGroup.of (rels := relations arms) u) (PresentedGroup.of v) := by
  let s := PresentedGroup.of (rels := relations arms) u
  let t := PresentedGroup.of (rels := relations arms) v
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using y_generator_sq arms u)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using y_generator_sq arms v)
  have hpi : (s*t)⁻¹ = s*t := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using y_nonadjacent_product_sq arms u v h)
  have he : t*s = s*t := by simpa only [mul_inv_rev,hsi,hti] using hpi
  exact he.symm

private theorem entry_far (arms : Arms) (i : Fin 3) {k : ℕ} (h : arms.length i = k)
    (d e : Fin k) (hde : d.val+2 ≤ e.val) : Commute (entry arms i h d) (entry arms i h e) := by
  apply nonadjacent_commute
  constructor
  · intro he
    have hv : d.val = e.val := congrArg
      (fun q : Node arms => match q with | none => 0 | some a => a.2.val) he
    omega
  · dsimp only [Adjacent]
    intro he
    change i = i ∧ (d.val+1 = e.val ∨ e.val+1 = d.val) at he
    omega

theorem arm_product_period_three (arms : Arms) (i : Fin 3) (h : arms.length i = 2) :
    (armProduct arms i)^3 = 1 := by
  rw [product_eq arms i 2 h]
  simpa only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one,mul_assoc] using
    entry_adjacent arms i h (0 : Fin 2) 1 (by decide)

theorem arm_product_period_four (arms : Arms) (i : Fin 3) (h : arms.length i = 3) :
    (armProduct arms i)^4 = 1 := by
  rw [product_eq arms i 3 h]
  simpa only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one,mul_assoc] using
    InvolutionChainShortPeriods.three_chain_period_four
      (entry arms i h 0) (entry arms i h 1) (entry arms i h 2)
      (entry_square arms i h 0) (entry_square arms i h 1) (entry_square arms i h 2)
      (entry_adjacent arms i h 0 1 (by decide)) (entry_adjacent arms i h 1 2 (by decide))
      (entry_far arms i h 0 2 (by decide))

theorem arm_product_period_five (arms : Arms) (i : Fin 3) (h : arms.length i = 4) :
    (armProduct arms i)^5 = 1 := by
  rw [product_eq arms i 4 h]
  simpa only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one,mul_assoc] using
    InvolutionChainShortPeriods.four_chain_period_five
      (entry arms i h 0) (entry arms i h 1) (entry arms i h 2) (entry arms i h 3)
      (entry_square arms i h 0) (entry_square arms i h 1)
      (entry_square arms i h 2) (entry_square arms i h 3)
      (entry_adjacent arms i h 0 1 (by decide)) (entry_adjacent arms i h 1 2 (by decide))
      (entry_adjacent arms i h 2 3 (by decide))
      (entry_far arms i h 0 2 (by decide)) (entry_far arms i h 0 3 (by decide))
      (entry_far arms i h 1 3 (by decide))

/-- Distinct actual arms commute entry-by-entry and hence as whole products. -/
theorem arm_products_commute (arms : Arms) (i j : Fin 3) (hij : i ≠ j) :
    Commute (armProduct arms i) (armProduct arms j) := by
  apply Commute.list_prod_left (armList arms i) (armProduct arms j)
  intro a ha
  apply Commute.list_prod_right (armList arms j) a
  intro b hb
  obtain ⟨d,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
  apply nonadjacent_commute
  constructor
  · intro he
    have he' : i = j := congrArg
      (fun q : Node arms => match q with | none => (0 : Fin 3) | some v => v.1) he
    exact hij he'
  · dsimp only [Adjacent]
    exact fun h => hij h.1

end SymmetricSubgroupAsymptotics.CFSGYArmProductPeriods
