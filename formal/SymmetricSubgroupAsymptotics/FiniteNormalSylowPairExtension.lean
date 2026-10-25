import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

/-! A disjoint pair of Sylows in a normal subgroup extends to an exact
pair of ambient Sylows. Their ambient intersection embeds in the same
normal quotient. Thus a small normal quotient controls the ONLY possible
intersection lost when passing from ambient Sylows to their restrictions.
No automorphism of the normal subgroup is lifted to the ambient group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteNormalSylowPairExtension
variable {G : Type*} [Group G]

theorem quotient_restriction_injective (N H : Subgroup G) [N.Normal]
    (h : H.comap N.subtype = ⊥) :
    Function.Injective ((QuotientGroup.mk' N).comp H.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro z hz
  have hzN : z.val ∈ N := (QuotientGroup.eq_one_iff z.val).mp hz
  have hm : (⟨z.val, hzN⟩ : N) ∈ H.comap N.subtype := z.property
  rw [h, Subgroup.mem_bot] at hm
  have he : (z.val : G) = 1 := congrArg (fun n : N => n.val) hm
  exact Subgroup.mem_bot.mpr (Subtype.ext he)

theorem card_le_index_of_comap_eq_bot [Finite G]
    (N H : Subgroup G) [N.Normal] (h : H.comap N.subtype = ⊥) :
    Nat.card H ≤ N.index :=
  Nat.card_le_card_of_injective _ (quotient_restriction_injective N H h)

theorem card_inf_le_index_of_disjoint_comap [Finite G]
    (N P Q : Subgroup G) [N.Normal]
    (h : P.comap N.subtype ⊓ Q.comap N.subtype = ⊥) :
    Nat.card (P ⊓ Q : Subgroup G) ≤ N.index := by
  apply card_le_index_of_comap_eq_bot N (P ⊓ Q)
  rwa [Subgroup.comap_inf]

theorem exists_sylow_pair [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (P Q : Sylow p N)
    (h : (P : Subgroup N) ⊓ (Q : Subgroup N) = ⊥) :
    ∃ R S : Sylow p G,
      (R : Subgroup G).comap N.subtype = (P : Subgroup N) ∧
      (S : Subgroup G).comap N.subtype = (Q : Subgroup N) ∧
      Nat.card ((R : Subgroup G) ⊓ (S : Subgroup G) : Subgroup G) ≤ N.index := by
  obtain ⟨R, hR⟩ := P.exists_comap_subtype_eq
  obtain ⟨S, hS⟩ := Q.exists_comap_subtype_eq
  refine ⟨R, S, hR, hS, ?_⟩
  apply card_inf_le_index_of_disjoint_comap N (R : Subgroup G) (S : Subgroup G)
  rwa [hR, hS]

end SymmetricSubgroupAsymptotics.FiniteNormalSylowPairExtension
