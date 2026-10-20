import SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalClassTwo

/-! Exact local commutators in the full physical four-point pair stabilizer.
These are selected point identities on 24 permutations, not normal-subgroup
classification. They support independent-coordinate original-kernel proofs. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalCommutators
open BinaryTwoLayerLocalClassTwo

def diagonal : Equiv.Perm Points where
  toFun x := (x.1,x.2+1)
  invFun x := (x.1,x.2+1)
  left_inv := by intro x; revert x; decide +kernel
  right_inv := by intro x; revert x; decide +kernel

theorem diagonal_preserves : Preserves diagonal := by
  intro x y h
  exact h

private theorem commutator_cases_rows :
    ∀ a b : Equiv.Perm Points, PairRows a → PairRows b →
      a*b*a⁻¹*b⁻¹=1 ∨ a*b*a⁻¹*b⁻¹=diagonal := by
  unfold PairRows
  decide +kernel

theorem commutator_cases
    (a b : Equiv.Perm Points) (ha : Preserves a) (hb : Preserves b) :
    a*b*a⁻¹*b⁻¹=1 ∨ a*b*a⁻¹*b⁻¹=diagonal :=
  commutator_cases_rows a b ((preserves_iff_pairRows a).mp ha)
    ((preserves_iff_pairRows b).mp hb)

private theorem noncentral_witness_rows :
    ∀ a : Equiv.Perm Points, PairRows a → a≠1 → a≠diagonal →
      ∃ b : Equiv.Perm Points, PairRows b ∧ a*b*a⁻¹*b⁻¹=diagonal := by
  unfold PairRows
  decide +kernel

/-- Every noncentral local element detects the SAME nontrivial center
coordinate by a commutator with an actual local pair-preserving element. -/
theorem noncentral_witness
    (a : Equiv.Perm Points) (ha : Preserves a) (h1 : a≠1) (hd : a≠diagonal) :
    ∃ b : Equiv.Perm Points, Preserves b ∧ a*b*a⁻¹*b⁻¹=diagonal := by
  obtain ⟨b,hb,hc⟩ := noncentral_witness_rows a
    ((preserves_iff_pairRows a).mp ha) h1 hd
  exact ⟨b,(preserves_iff_pairRows b).mpr hb,hc⟩

private theorem diagonal_commutes_rows :
    ∀ a : Equiv.Perm Points, PairRows a → diagonal*a=a*diagonal := by
  unfold PairRows
  decide +kernel

theorem diagonal_commutes
    (a : Equiv.Perm Points) (ha : Preserves a) : diagonal*a=a*diagonal :=
  diagonal_commutes_rows a ((preserves_iff_pairRows a).mp ha)

end SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalCommutators
