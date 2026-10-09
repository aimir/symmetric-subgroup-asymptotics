import SymmetricSubgroupAsymptotics.Non2PreE7LinearThreeGroup

/-!
# Normal Klein four subgroups in `GL₂(3)`

A faithful Klein four subgroup of the ternary plane is the diagonal sign
group in a suitable basis.  Its full linear normalizer is dihedral of order
eight.  The finite statement below is made on the literal `2 × 2` matrices;
later files use it only through the intrinsic hypotheses "order four" and
"exponent two".

This is the small linear fact which rules out the order-sixteen Sylow group
when a binary top acts on a two-dimensional ternary section and normalizes
the surviving pair kernel.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace LinearThree

/-- The normalizer of every elementary abelian subgroup of order four in
`GL₂(3)` has order at most eight. -/
set_option maxRecDepth 100000 in
theorem klein_normalizer_card_le_eight
    (K : Subgroup GL3)
    (hcard : Nat.card K = 4)
    (hsquare : ∀ k : K, k ^ 2 = 1) :
    Nat.card (Subgroup.normalizer (K : Set GL3)) ≤ 8 := by
  revert K
  decide +kernel

/-- Any subgroup of `GL₂(3)` which normalizes an elementary abelian
order-four subgroup has order at most eight. -/
theorem card_le_eight_of_normalizes_klein
    (H K : Subgroup GL3)
    (hKH : K ≤ H)
    (hnormal : (K.subgroupOf H).Normal)
    (hcard : Nat.card K = 4)
    (hsquare : ∀ k : K, k ^ 2 = 1) :
    Nat.card H ≤ 8 := by
  have hle : H ≤ Subgroup.normalizer (K : Set GL3) := by
    intro h hh
    apply Subgroup.mem_normalizer_iff.mpr
    intro k
    constructor
    · intro hk
      exact (Subgroup.normal_subgroupOf_iff hKH).mp hnormal
        k h hk hh
    · intro hk
      have hback := (Subgroup.normal_subgroupOf_iff hKH).mp hnormal
        (h * k * h⁻¹) h⁻¹ hk (H.inv_mem hh)
      simpa only [inv_inv, mul_assoc, inv_mul_cancel_left,
        mul_inv_cancel_right, inv_mul_cancel, mul_one] using hback
  exact (Nat.card_le_card_of_injective
      (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)).trans
    (klein_normalizer_card_le_eight K hcard hsquare)

end LinearThree
end SymmetricSubgroupAsymptotics

end
