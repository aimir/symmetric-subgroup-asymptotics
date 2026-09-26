import SymmetricSubgroupAsymptotics.BinaryPhysicalPairCertificate
import SymmetricSubgroupAsymptotics.BinaryNormalCharacterCriterion
import SymmetricSubgroupAsymptotics.BinaryCheckedTransport

/-! Exact alternatives for one original normal subgroup. The carrier menu
is supplied literally on the same physical set; its auxiliary quotient
degree is separate. This predicate makes no analytic counting claim. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- The pair and character branches use the original `U` and `U ⧸ N`.
The carrier branch identifies both its source and marked kernel inside
the original permutation group, rather than only up to isomorphism. -/
def BinaryFiniteEntry {w q : ℕ} {κ : Type*}
    (carriers : κ → CheckedPermutationCarrier w q)
    (U : Subgroup (Equiv.Perm (Fin w))) (N : Subgroup U) [N.Normal] : Prop :=
  Nonempty (BinaryPhysicalPairCertificate U N) ∨
  Nonempty (BinaryNormalCharacterCriterion (U ⧸ N) w) ∨
  ∃ i, (carriers i).source=U ∧ (carriers i).axis=N.map U.subtype

namespace BinaryFiniteEntry

/-- Eliminate a finite entry only on its exact original normal subgroup.
No branch can change the action degree or the original quotient. -/
theorem elim {w q : ℕ} {κ : Type*}
    {carriers : κ → CheckedPermutationCarrier w q}
    {U : Subgroup (Equiv.Perm (Fin w))} {N : Subgroup U} [N.Normal]
    (h : BinaryFiniteEntry carriers U N) {P : Prop}
    (hpair : BinaryPhysicalPairCertificate U N → P)
    (hcharacter : BinaryNormalCharacterCriterion (U ⧸ N) w → P)
    (hcarrier : ∀ i, (carriers i).source=U →
      (carriers i).axis=N.map U.subtype → P) : P := by
  change Nonempty (BinaryPhysicalPairCertificate U N) ∨
    Nonempty (BinaryNormalCharacterCriterion (U ⧸ N) w) ∨
    (∃ i, (carriers i).source=U ∧ (carriers i).axis=N.map U.subtype) at h
  rcases h with hp | hc
  · obtain ⟨C⟩ := hp
    exact hpair C
  · rcases hc with hc | ht
    · obtain ⟨C⟩ := hc
      exact hcharacter C
    · obtain ⟨i,hs,ha⟩ := ht
      exact hcarrier i hs ha

end BinaryFiniteEntry
end SymmetricSubgroupAsymptotics
