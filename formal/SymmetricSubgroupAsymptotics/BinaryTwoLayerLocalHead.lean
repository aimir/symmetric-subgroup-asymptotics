import SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalCommutators

/-! The exact two-bit abelian head of the literal four-point pair
stabilizer. One bit is the permutation of the two rows, and the other is
the sum of their internal offsets. The common kernel is its actual center. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalHead
open BinaryTwoLayerLocalClassTwo BinaryTwoLayerLocalCommutators

/-- Actual point coordinates, requiring no chosen abstract D8 isomorphism. -/
def head (a : Equiv.Perm Points) : Points :=
  ((a (0,0)).1,(a (0,0)).2+(a (1,0)).2)

theorem head_one : head (1 : Equiv.Perm Points)=0 := by decide +kernel

private theorem head_mul_rows :
    ∀ a b : Equiv.Perm Points, PairRows a → PairRows b →
      head (a*b)=head a+head b := by
  unfold PairRows
  decide +kernel

theorem head_mul (a b : Equiv.Perm Points) (ha : Preserves a) (hb : Preserves b) :
    head (a*b)=head a+head b :=
  head_mul_rows a b ((preserves_iff_pairRows a).mp ha) ((preserves_iff_pairRows b).mp hb)

private theorem head_zero_rows :
    ∀ a : Equiv.Perm Points, PairRows a → (head a=0 ↔ a=1 ∨ a=diagonal) := by
  unfold PairRows
  decide +kernel

theorem head_zero_iff (a : Equiv.Perm Points) (ha : Preserves a) :
    head a=0 ↔ a=1 ∨ a=diagonal :=
  head_zero_rows a ((preserves_iff_pairRows a).mp ha)

private theorem head_surjective_rows :
    ∀ v : Points, ∃ a : Equiv.Perm Points, PairRows a ∧ head a=v := by
  unfold PairRows
  decide +kernel

/-- Every binary head value has a literal pair-preserving permutation lift. -/
theorem head_surjective (v : Points) :
    ∃ a : Equiv.Perm Points, Preserves a ∧ head a=v := by
  obtain ⟨a,ha,hv⟩ := head_surjective_rows v
  exact ⟨a,(preserves_iff_pairRows a).mpr ha,hv⟩

private theorem head_conjugate_rows :
    ∀ a b : Equiv.Perm Points, PairRows a → PairRows b →
      head (a*b*a⁻¹)=head b := by
  unfold PairRows
  decide +kernel

/-- Physical changes of local pair coordinates do not change this head. -/
theorem head_conjugate (a b : Equiv.Perm Points) (ha : Preserves a) (hb : Preserves b) :
    head (a*b*a⁻¹)=head b :=
  head_conjugate_rows a b ((preserves_iff_pairRows a).mp ha)
    ((preserves_iff_pairRows b).mp hb)

end SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalHead
