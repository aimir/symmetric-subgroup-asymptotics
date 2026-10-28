import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound
import SymmetricSubgroupAsymptotics.ProperSubnormalSimpleExtensionClassBound

/-! A proper-index lower bound for a centerless normal subgroup controls
all subgroups of the ambient extension. The intersection is kept literal:
when it is proper we use its order, and when it is full we use the class
equation in the normal subgroup. No class-count monotonicity is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NormalCenterlessIndexSubgroupClassBound

variable {G : Type*} [Group G] [Finite G]

theorem class_card_le (S : Subgroup G) [S.Normal] (L : ℕ) (hL : 0 < L)
    (hcenter : Subgroup.center S = ⊥)
    (hindex : ∀ K : Subgroup S, K ≠ ⊤ → L ≤ K.index)
    (H : Subgroup G) :
    Nat.card (ConjClasses H) ≤
      (Nat.card S / L + 1) * Nat.card (G ⧸ S) := by
  let f : H →* G ⧸ S := (QuotientGroup.mk' S).comp H.subtype
  let K : Subgroup S := H.subgroupOf S
  let e : f.ker ≃* K :=
    ProperSubnormalSimpleExtensionClassBound.restrictionKernelEquiv S H
  have hker : Nat.card (ConjClasses f.ker) ≤ Nat.card S / L + 1 := by
    by_cases hK : K = ⊤
    · let eS : f.ker ≃* S := e.trans ((MulEquiv.subgroupCongr hK).trans Subgroup.topEquiv)
      have hc : Nat.card (ConjClasses f.ker) ≤ Nat.card (ConjClasses S) :=
        Nat.card_le_card_of_surjective (ConjClasses.map eS.symm.toMonoidHom)
          (ConjClasses.map_surjective eS.symm.surjective)
      exact hc.trans (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
        L hL hcenter hindex)
    · have hKcard : Nat.card K ≤ Nat.card S / L := by
        apply (Nat.le_div_iff_mul_le hL).mpr
        calc
          Nat.card K * L ≤ Nat.card K * K.index :=
            Nat.mul_le_mul_left _ (hindex K hK)
          _ = Nat.card S := K.card_mul_index
      have hc : Nat.card (ConjClasses f.ker) ≤ Nat.card f.ker :=
        Nat.card_le_card_of_surjective (@ConjClasses.mk f.ker _) ConjClasses.mk_surjective
      have he : Nat.card f.ker = Nat.card K := Nat.card_congr e.toEquiv
      exact (hc.trans (he.le.trans hKcard)).trans (Nat.le_succ _)
  have hrange : Nat.card (ConjClasses f.range) ≤ Nat.card (G ⧸ S) :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk f.range _) ConjClasses.mk_surjective).trans
      (Nat.card_le_card_of_injective f.range.subtype Subtype.val_injective)
  exact (conjugacyClass_card_le_kernel_mul_range f).trans (Nat.mul_le_mul hker hrange)

end SymmetricSubgroupAsymptotics.NormalCenterlessIndexSubgroupClassBound
