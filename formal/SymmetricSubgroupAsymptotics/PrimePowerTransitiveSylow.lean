import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.Index

/-! A finite transitive action of prime-power degree has a transitive
Sylow subgroup. Extend a Sylow subgroup of a point stabilizer, then compare
the exact stabilizer indices by Sylow cardinalities. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem exists_transitive_sylow
    {G X : Type*} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    (p d : ℕ) [Fact p.Prime] (hdegree : Nat.card X = p ^ d) :
    ∃ P : Sylow p G, MulAction.IsPretransitive P X := by
  classical
  let x : X := Classical.arbitrary X
  let H : Subgroup G := MulAction.stabilizer G x
  let Q : Sylow p H := Classical.choice (Sylow.nonempty)
  obtain ⟨P, hPQ⟩ := Q.exists_comap_subtype_eq
  let T : Subgroup P := MulAction.stabilizer P x
  let e : T ≃* (P : Subgroup G).comap H.subtype :=
    { toFun := fun s => ⟨⟨s.val.val, s.property⟩, s.val.property⟩
      invFun := fun s => ⟨⟨s.val.val, s.property⟩, s.val.property⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      map_mul' := fun _ _ => Subtype.ext (Subtype.ext rfl) }
  have hstab : Nat.card T = Nat.card Q := by
    have h := Nat.card_congr e.toEquiv
    rw [hPQ] at h
    exact h
  have hGcard : Nat.card G = Nat.card H * p ^ d := by
    have h := H.card_mul_index
    rw [MulAction.index_stabilizer_of_transitive G x, hdegree] at h
    exact h.symm
  have hexp : (Nat.card G).factorization p = (Nat.card H).factorization p + d := by
    rw [hGcard, Nat.factorization_mul Nat.card_pos.ne'
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), Finsupp.add_apply,
      Nat.factorization_pow_self (Fact.out : p.Prime)]
  have hPcard : Nat.card P = Nat.card Q * p ^ d := by
    rw [P.card_eq_multiplicity, Q.card_eq_multiplicity, hexp, pow_add]
  have hindex : T.index = Nat.card X := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := T))
    calc
      Nat.card T * T.index = Nat.card P := T.card_mul_index
      _ = Nat.card T * Nat.card X := by rw [hPcard, hstab, hdegree]
  have horbit : MulAction.orbit P x = Set.univ := by
    apply (Set.eq_univ_iff_ncard _).mpr
    exact (MulAction.index_stabilizer P x).symm.trans hindex
  exact ⟨P, (MulAction.isPretransitive_iff_orbit_eq_univ (G := P) x).mpr horbit⟩

end SymmetricSubgroupAsymptotics

end
