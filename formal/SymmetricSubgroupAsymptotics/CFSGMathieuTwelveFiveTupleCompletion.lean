import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFiveTransversalCover
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSharpFiveRigidity

/-! Computable completion of an arbitrary injective ordered five-tuple by
the SAME original M12 transversal words. No finite group search, abstract
model recognition, or Witt-preservation converse is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFiveTupleCompletion
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelveFiveTransversalCover
open CFSGMathieuTwelveSharpFiveRigidity

private theorem inverse_ne (g : M12) (t : Fin 5 ↪ Fin 12) (j i : Fin 5)
    (hne : j ≠ i) (hp : g.val (standardBase i) = t i) :
    g.val.symm (t j) ≠ standardBase i := by
  intro he
  have h := congrArg g.val he
  rw [Equiv.apply_symm_apply,hp] at h
  exact (t.injective.ne hne) h

def prefix1 (t : Fin 5 ↪ Fin 12) : M12 := first (t 0)

private theorem prefix1_zero (t : Fin 5 ↪ Fin 12) : (prefix1 t).val 0 = t 0 :=
  first_zero _

def address2 (t : Fin 5 ↪ Fin 12) : Second :=
  ⟨(prefix1 t).val.symm (t 1),inverse_ne (prefix1 t) t 1 0 (by decide) (prefix1_zero t)⟩

def prefix2 (t : Fin 5 ↪ Fin 12) : M12 := prefix1 t * second (address2 t)

private theorem prefix2_zero (t : Fin 5 ↪ Fin 12) : (prefix2 t).val 0 = t 0 := by
  simp only [prefix2,Subgroup.coe_mul,Equiv.Perm.mul_apply,second_zero,prefix1_zero]

private theorem prefix2_one (t : Fin 5 ↪ Fin 12) : (prefix2 t).val 1 = t 1 := by
  simp only [prefix2,Subgroup.coe_mul,Equiv.Perm.mul_apply,second_one]
  change (prefix1 t).val ((prefix1 t).val.symm (t 1)) = t 1
  exact Equiv.apply_symm_apply _ _

def address3 (t : Fin 5 ↪ Fin 12) : Third :=
  ⟨(prefix2 t).val.symm (t 2),
    inverse_ne (prefix2 t) t 2 0 (by decide) (prefix2_zero t),
    inverse_ne (prefix2 t) t 2 1 (by decide) (prefix2_one t)⟩

def prefix3 (t : Fin 5 ↪ Fin 12) : M12 := prefix2 t * third (address3 t)

private theorem prefix3_zero (t : Fin 5 ↪ Fin 12) : (prefix3 t).val 0 = t 0 := by
  simp only [prefix3,Subgroup.coe_mul,Equiv.Perm.mul_apply,third_zero,prefix2_zero]

private theorem prefix3_one (t : Fin 5 ↪ Fin 12) : (prefix3 t).val 1 = t 1 := by
  simp only [prefix3,Subgroup.coe_mul,Equiv.Perm.mul_apply,third_one,prefix2_one]

private theorem prefix3_two (t : Fin 5 ↪ Fin 12) : (prefix3 t).val 2 = t 2 := by
  simp only [prefix3,Subgroup.coe_mul,Equiv.Perm.mul_apply,third_two]
  change (prefix2 t).val ((prefix2 t).val.symm (t 2)) = t 2
  exact Equiv.apply_symm_apply _ _

def address4 (t : Fin 5 ↪ Fin 12) : Fourth :=
  ⟨(prefix3 t).val.symm (t 3),
    inverse_ne (prefix3 t) t 3 0 (by decide) (prefix3_zero t),
    inverse_ne (prefix3 t) t 3 1 (by decide) (prefix3_one t),
    inverse_ne (prefix3 t) t 3 2 (by decide) (prefix3_two t)⟩

def prefix4 (t : Fin 5 ↪ Fin 12) : M12 := prefix3 t * fourth (address4 t)

private theorem prefix4_zero (t : Fin 5 ↪ Fin 12) : (prefix4 t).val 0 = t 0 := by
  simp only [prefix4,Subgroup.coe_mul,Equiv.Perm.mul_apply,fourth_zero,prefix3_zero]

private theorem prefix4_one (t : Fin 5 ↪ Fin 12) : (prefix4 t).val 1 = t 1 := by
  simp only [prefix4,Subgroup.coe_mul,Equiv.Perm.mul_apply,fourth_one,prefix3_one]

private theorem prefix4_two (t : Fin 5 ↪ Fin 12) : (prefix4 t).val 2 = t 2 := by
  simp only [prefix4,Subgroup.coe_mul,Equiv.Perm.mul_apply,fourth_two,prefix3_two]

private theorem prefix4_three (t : Fin 5 ↪ Fin 12) : (prefix4 t).val 3 = t 3 := by
  simp only [prefix4,Subgroup.coe_mul,Equiv.Perm.mul_apply,fourth_three]
  change (prefix3 t).val ((prefix3 t).val.symm (t 3)) = t 3
  exact Equiv.apply_symm_apply _ _

-- Keep the completed four-stage word abstract during final point elaboration.
attribute [irreducible] prefix4

def address5 (t : Fin 5 ↪ Fin 12) : Fifth :=
  ⟨(prefix4 t).val.symm (t 4),
    inverse_ne (prefix4 t) t 4 0 (by decide) (prefix4_zero t),
    inverse_ne (prefix4 t) t 4 1 (by decide) (prefix4_one t),
    inverse_ne (prefix4 t) t 4 2 (by decide) (prefix4_two t),
    inverse_ne (prefix4 t) t 4 3 (by decide) (prefix4_three t)⟩

def complete (t : Fin 5 ↪ Fin 12) : M12 := prefix4 t * fifth (address5 t)

private theorem hom_mul_apply {G X : Type*} [Group G] (rho : G →* Equiv.Perm X)
    (g h : G) (p : X) : rho (g*h) p = rho g (rho h p) := by
  rw [rho.map_mul]
  rfl

private theorem complete_apply (t : Fin 5 ↪ Fin 12) (p : Fin 12) :
    (complete t).val p = (prefix4 t).val ((fifth (address5 t)).val p) :=
  hom_mul_apply M12Subgroup.subtype (prefix4 t) (fifth (address5 t)) p

attribute [irreducible] complete

theorem complete_points (t : Fin 5 ↪ Fin 12) (i : Fin 5) :
    (complete t).val (standardBase i) = t i := by
  fin_cases i
  · change (complete t).val 0 = t 0
    rw [complete_apply,fifth_zero]
    exact prefix4_zero t
  · change (complete t).val 1 = t 1
    rw [complete_apply,fifth_one]
    exact prefix4_one t
  · change (complete t).val 2 = t 2
    rw [complete_apply,fifth_two]
    exact prefix4_two t
  · change (complete t).val 3 = t 3
    rw [complete_apply,fifth_three]
    exact prefix4_three t
  · change (complete t).val 4 = t 4
    rw [complete_apply,fifth_four]
    change (prefix4 t).val ((prefix4 t).val.symm (t 4)) = t 4
    exact Equiv.apply_symm_apply _ _

theorem complete_eq_of_points (t : Fin 5 ↪ Fin 12) (g : M12)
    (hg : ∀ i : Fin 5, g.val (standardBase i) = t i) : complete t = g := by
  apply eq_of_agree_five standardBase
  intro i
  rw [complete_points,hg]

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFiveTupleCompletion
