import SymmetricSubgroupAsymptotics.ProperSubnormalSimpleExtensionClassBound
import SymmetricSubgroupAsymptotics.AlternatingNaturalClassExtraGap
import SymmetricSubgroupAsymptotics.SymmetricComponentDegreeLower
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-! Proper subnormal budgets for an actual component abstractly
isomorphic to S_m, in any faithful permutation degree. The actual
quotient/intersection bound supplies the extra exponent. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SymmetricComponentProperSubnormalClassGap

theorem proper_subnormal_class_card_le_alternating (m : ℕ) (hm : 5 ≤ m)
    (L : Subgroup (Equiv.Perm (Fin m))) (hL : L.IsSubnormal) (hne : L ≠ ⊤) :
    Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses (alternatingGroup (Fin m))) := by
  letI : Nontrivial (Fin m) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < m by omega))
  letI : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simpa only [Nat.card_fin] using hm)
  have hh := ProperSubnormalSimpleExtensionClassBound.twice_class_card_le_quotient_mul_simple
    (alternatingGroup (Fin m)) L hL hne
  have hq : Nat.card (Equiv.Perm (Fin m) ⧸ alternatingGroup (Fin m)) = 2 := by
    rw [← Subgroup.index_eq_card, alternatingGroup.index_eq_two]
  rw [hq] at hh
  omega

theorem proper_subnormal_class_cube_le {Y : Type*} [Finite Y]
    (C : Subgroup (Equiv.Perm Y)) (m : ℕ) (hm : 5 ≤ m)
    (e : C ≃* Equiv.Perm (Fin m)) (L : Subgroup C)
    (hL : L.IsSubnormal) (hne : L ≠ ⊤) :
    Nat.card (ConjClasses L)^3 ≤ 5^(Nat.card Y-2) := by
  have hmdegree := SymmetricComponentDegreeLower.degree_le C m (by omega) e
  have hmapped : (L.map e.toMonoidHom).IsSubnormal := hL.map e.surjective
  have hproper : L.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hne
    apply top_unique
    intro x _
    apply (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) (K := L) (x := x)
      (show Function.Injective e.toMonoidHom from e.injective)).mp
    rw [ht]
    trivial
  have hc : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses (L.map e.toMonoidHom)) :=
    Nat.card_le_card_of_surjective (ConjClasses.map (e.subgroupMap L).symm.toMonoidHom)
      (ConjClasses.map_surjective (e.subgroupMap L).symm.surjective)
  have ha := proper_subnormal_class_card_le_alternating m hm
    (L.map e.toMonoidHom) hmapped hproper
  calc
    Nat.card (ConjClasses L)^3 ≤
        Nat.card (ConjClasses (alternatingGroup (Fin m)))^3 :=
      Nat.pow_le_pow_left (hc.trans ha) 3
    _ ≤ 5^(m-2) := AlternatingNaturalClassExtraGap.alternating_class_cube_le m hm
    _ ≤ 5^(Nat.card Y-2) :=
      Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hmdegree 2)

end SymmetricSubgroupAsymptotics.SymmetricComponentProperSubnormalClassGap
