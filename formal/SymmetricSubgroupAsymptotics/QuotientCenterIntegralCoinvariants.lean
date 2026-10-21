import SymmetricSubgroupAsymptotics.NormalIntegralCoinvariantExtension
import SymmetricSubgroupAsymptotics.SmallBinaryNormalFBounds

/-! The full original preimage of the quotient centre pays its complete
integral coinvariant order. Higher cyclic factors are retained, and the
preimage has index at least four for a nonabelian quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics
variable {G : Type} [Group G] [Finite G]

theorem quotient_center_card_le_integral_coinvariant_preimage
    (N : Subgroup G) [N.Normal] :
    Nat.card (Subgroup.center (G ⧸ N))≤normalIntegralCoinvariantOrder
      ((Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N)) := by
  let q := QuotientGroup.mk' N
  let Z := (Subgroup.center (G ⧸ N)).comap q
  let B := (⁅Z,(⊤ : Subgroup G)⁆).subgroupOf Z
  have hcomm : ⁅Z,(⊤ : Subgroup G)⁆≤q.ker := by
    apply Subgroup.commutator_le.mpr
    intro z hz g _
    change q ⁅z,g⁆=1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp (show q z∈Subgroup.center (G ⧸ N) from hz) (q g)).symm
  let f : Z →* Subgroup.center (G ⧸ N) := {
    toFun := fun z => ⟨q z,z.property⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun a b => Subtype.ext (map_mul q (a : G) (b : G)) }
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective N z.val
    have hgZ : g∈Z := by change q g∈Subgroup.center (G ⧸ N);rw [hg];exact z.property
    exact ⟨⟨g,hgZ⟩,Subtype.ext hg⟩
  have hB : B≤f.ker := by
    intro z hz
    apply Subtype.ext
    exact hcomm hz
  have hc := Nat.card_le_card_of_surjective (QuotientGroup.lift B f hB)
    (QuotientGroup.lift_surjective_of_surjective B f hf hB)
  exact hc

/-- This consumer is valid for every original normal denominator; it does
not infer a full integral order from an elementary head bound. -/
theorem quotient_center_card_le_of_large_index_integral_bound
    (b : ℕ)
    (hbound : ∀ A : Subgroup G,∀ [A.Normal],2<A.index → normalIntegralCoinvariantOrder A≤b)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N,a*b=b*a) :
    Nat.card (Subgroup.center (G ⧸ N))≤b := by
  let Z := (Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N)
  have hi := SmallBinaryNormalFBounds.nonabelian_center_index_four_le hnonab
  have hindex : 2<Z.index := by
    rw [show Z.index=(Subgroup.center (G ⧸ N)).index from
      (Subgroup.center (G ⧸ N)).index_comap_of_surjective (QuotientGroup.mk'_surjective N)]
    omega
  exact (quotient_center_card_le_integral_coinvariant_preimage N).trans (hbound Z hindex)

end SymmetricSubgroupAsymptotics
