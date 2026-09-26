import SymmetricSubgroupAsymptotics.BinaryTargetOrderFusion
import SymmetricSubgroupAsymptotics.BinarySylowCoverage

/-! Order bounds accept entire downward classes of original actions.

Every normal quotient of an action of order at most `2^a` has a proved
target-order envelope whenever `2*a < w`. The action registry therefore
needs only the transitive index-prime children above that order bound.
Normal registries can also stop once the original quotient index is small.
Neither result asserts coverage of the remaining high-order records.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics
namespace BinaryOrderPrunedCoverage

/-- An actual quotient order bound supplies the marker gap directly. -/
def certificateOfQuotientCard {w a : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (N : Subgroup U) [N.Normal]
    (hcard : Nat.card (U ⧸ N) ≤ 2^a) (hgap : 2*a < w) :
    BinaryTargetOrderCertificate U N := by
  have hlog : Nat.log 2 (Nat.card (U ⧸ N)) ≤ a := by
    simpa only [Nat.log_pow (by decide : 1 < 2)] using
      (Nat.log_mono_right (b := 2) hcard)
  exact ⟨(Nat.mul_le_mul_left 2 hlog).trans_lt hgap⟩

/-- Every literal original normal inherits the same source-order bound. -/
def certificateOfCard {w a : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (N : Subgroup U) [N.Normal]
    (hcard : Nat.card U ≤ 2^a) (hgap : 2*a < w) :
    BinaryTargetOrderCertificate U N :=
  certificateOfQuotientCard U N
    ((Nat.card_le_card_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans hcard) hgap

/-- All original axes are installed in the checked pair/order interface.
The selection is fixed before any exterior group or survival predicate. -/
def selectionOfCard {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (a : ℕ)
    (hcard : Nat.card U ≤ 2^a) (hgap : 2*a < w) :
    BinaryPairOrderSelection U := fun N =>
  some (.inr (certificateOfCard U N.1 hcard hgap))

theorem selectionOfCard_ne_none {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (a : ℕ)
    (hcard : Nat.card U ≤ 2^a) (hgap : 2*a < w)
    (N : {N : Subgroup U // N.Normal}) :
    selectionOfCard U a hcard hgap N ≠ none := by
  simp [selectionOfCard]

theorem selectionOfCard_prefixDegree {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (a : ℕ)
    (hcard : Nat.card U ≤ 2^a) (hgap : 2*a < w)
    (N : {N : Subgroup U // N.Normal}) :
    (selectionOfCard U a hcard hgap).prefixDegree N =
      2 * Nat.log 2 (Nat.card (U ⧸ N.1)) := rfl

theorem selectionOfCard_liftConstant {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (a : ℕ)
    (hcard : Nat.card U ≤ 2^a) (hgap : 2*a < w)
    (N : {N : Subgroup U // N.Normal}) :
    (selectionOfCard U a hcard hgap).liftConstant N = 1 := rfl

/-- Every subgroup of a bounded-order original action is accepted on the
same physical points. No transitivity or abstract action replacement is used. -/
def selectionOfSubgroupCard {w : ℕ}
    (U H : Subgroup (Equiv.Perm (Fin w))) (hHU : H ≤ U) (a : ℕ)
    (hcard : Nat.card U ≤ 2^a) (hgap : 2*a < w) :
    BinaryPairOrderSelection H :=
  selectionOfCard H a
    ((Nat.card_le_card_of_injective (Subgroup.inclusion hHU)
      (Subgroup.inclusion_injective hHU)).trans hcard) hgap

/-- The complete original normal set of every degree-sixteen action of
order at most 128 has the checked target-order selection. -/
def sixteenSelection (U : Subgroup (Equiv.Perm (Fin 16)))
    (hcard : Nat.card U ≤ 128) : BinaryPairOrderSelection U :=
  selectionOfCard U 7 hcard (by decide)

/-- The corresponding degree-eight threshold includes every regular action. -/
def eightSelection (U : Subgroup (Equiv.Perm (Fin 8)))
    (hcard : Nat.card U ≤ 8) : BinaryPairOrderSelection U :=
  selectionOfCard U 3 hcard (by decide)

/-- The registry only needs children above `cap`. All actions below the
cap form one accepted alternative, including unlisted descendants. -/
theorem action_registry_complete_above_order
    {Ω I : Type*} [Finite Ω] {p : ℕ} [Fact p.Prime]
    (actions : I → Subgroup (Equiv.Perm Ω)) (P : Sylow p (Equiv.Perm Ω))
    (root : I) (hroot : actions root = (P : Subgroup (Equiv.Perm Ω)))
    (cap : ℕ)
    (hchildren : ∀ i, ∀ K : Subgroup (Equiv.Perm Ω),
      K < actions i → K.relIndex (actions i) = p →
      PermutationSubgroupTransitive K → cap < Nat.card K →
        ActionRegistryCovered actions K)
    (H : Subgroup (Equiv.Perm Ω)) (hH : IsPGroup p H)
    (ht : PermutationSubgroupTransitive H) :
    Nat.card H ≤ cap ∨ ActionRegistryCovered actions H := by
  by_cases hsmall : Nat.card H ≤ cap
  · exact Or.inl hsmall
  · apply Or.inr
    refine pGroup_action_registry_complete actions P root hroot
      (fun K => PermutationSubgroupTransitive K ∧ cap < Nat.card K)
      ?_ ?_ ?_ H hH ?_
    · intro K L hKL hK
      exact ⟨permutationSubgroupTransitive_mono K L hKL hK.1,
        hK.2.trans_le (Nat.card_le_card_of_injective
          (Subgroup.inclusion hKL) (Subgroup.inclusion_injective hKL))⟩
    · intro g K hK
      refine ⟨permutationSubgroupTransitive_conjugate g K hK.1, ?_⟩
      have hc : Nat.card K = Nat.card ↥(MulAut.conj g • K) :=
        Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) K).toEquiv
      rw [← hc]
      exact hK.2
    · intro i K hKi hindex hK
      exact hchildren i K hKi hindex hK.1 hK.2
    · exact ⟨ht, lt_of_not_ge hsmall⟩

/-- A normal registry may stop at small quotient index. All larger original
normals remain accepted because index is antitone under inclusion. -/
theorem normal_registry_complete_above_index
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (registry : Set (Subgroup G))
    (hbot : ⊥ ∈ registry)
    (cap : ℕ)
    (hchildren : ∀ N ∈ registry, ∀ _hN : N.Normal, ∀ z : G ⧸ N,
      z ∈ Subgroup.center (G ⧸ N) → orderOf z = p →
      ((Subgroup.zpowers z).comap (QuotientGroup.mk' N)).index ≤ cap ∨
        (Subgroup.zpowers z).comap (QuotientGroup.mk' N) ∈ registry)
    (L : Subgroup G) [L.Normal] : L.index ≤ cap ∨ L ∈ registry := by
  let enlarged : Set (Subgroup G) :=
    {N | N.Normal ∧ (N.index ≤ cap ∨ N ∈ registry)}
  have hroot : (⊥ : Subgroup G) ∈ enlarged :=
    ⟨inferInstance, Or.inr hbot⟩
  have hnorm : ∀ N ∈ enlarged, N.Normal := fun _ hN => hN.1
  have hsteps : ∀ N ∈ enlarged, ∀ _hN : N.Normal, ∀ z : G ⧸ N,
      z ∈ Subgroup.center (G ⧸ N) → orderOf z = p →
      (Subgroup.zpowers z).comap (QuotientGroup.mk' N) ∈ enlarged := by
    intro N hN hnormalN z hzc hzp
    have hprop := central_prime_preimage_properties N z hzc hzp
    refine ⟨hprop.1, ?_⟩
    rcases hN.2 with hsmall | hregistered
    · apply Or.inl
      have hle : N ≤ (Subgroup.zpowers z).comap (QuotientGroup.mk' N) := by
        simpa only [QuotientGroup.ker_mk'] using
          (Subgroup.ker_le_comap (QuotientGroup.mk' N) (Subgroup.zpowers z))
      exact (Subgroup.index_antitone hle).trans hsmall
    · exact hchildren N hregistered hnormalN z hzc hzp
  exact (pGroup_normal_registry_complete hG enlarged hroot hnorm hsteps L).2

end BinaryOrderPrunedCoverage
end SymmetricSubgroupAsymptotics

end
