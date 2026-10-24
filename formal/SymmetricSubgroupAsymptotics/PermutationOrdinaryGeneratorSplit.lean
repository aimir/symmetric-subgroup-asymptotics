import SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! Ordinary generation splits through the literal restriction image
on an invariant set and the actual kernel acting on its complement.
This is an induction tool, not a proof of the sharp all-group theorem:
its S3 exceptional factors still require generator sharing. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PermutationOrdinaryGeneratorSplit
open PermutationCharacterRankSplit

private theorem rank_le_of_surjective {G H : Type} [Group G] [Finite G] [Group H]
    (f : G→*H) (hf : Function.Surjective f) : MarkedC4.genRank H≤MarkedC4.genRank G := by
  classical
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  let T : Finset H := S.image f
  have hT : Subgroup.closure (T:Set H)=⊤ := by
    have he := congrArg (Subgroup.map f) hgen
    simpa only [T,Finset.coe_image,MonoidHom.map_closure,
      Subgroup.map_top_of_surjective f hf] using he
  exact (MarkedC4.genRank_le hT).trans (Finset.card_image_le.trans hS.le)

theorem genRank_le_image_add_kernel {G X : Type} [Group G] [Finite G] [MulAction G X]
    (S : SubMulAction G X) :
    MarkedC4.genRank G≤MarkedC4.genRank (Image S)+MarkedC4.genRank (Kernel S) := by
  let e : G⧸Kernel S≃*Image S :=
    QuotientGroup.quotientKerEquivOfSurjective (projection S) (projection_surjective S)
  have hq := rank_le_of_surjective e.symm.toMonoidHom e.symm.surjective
  calc
    MarkedC4.genRank G≤MarkedC4.genRank (Kernel S)+MarkedC4.genRank (G⧸Kernel S) :=
      MarkedC4.genRank_le_of_normal (Kernel S)
    _≤MarkedC4.genRank (Kernel S)+MarkedC4.genRank (Image S) := Nat.add_le_add_left hq _
    _=MarkedC4.genRank (Image S)+MarkedC4.genRank (Kernel S) := Nat.add_comm _ _

theorem genRank_le_card_div {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (S : SubMulAction G X) (d : ℕ)
    (hI : MarkedC4.genRank (Image S)≤Nat.card S/d)
    (hK : MarkedC4.genRank (Kernel S)≤Nat.card ↥(Sᶜ)/d) :
    MarkedC4.genRank G≤Nat.card X/d := by
  refine (genRank_le_image_add_kernel S).trans ((Nat.add_le_add hI hK).trans ?_)
  simpa only [card_split S] using Nat.add_div_le_add_div (Nat.card S) (Nat.card ↥(Sᶜ)) d

theorem half_degree_of_smaller_actions {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (S : SubMulAction G X)
    (hS : (S:Set X).Nonempty) (hC : (Sᶜ:Set X).Nonempty)
    (hsmaller : ∀(H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y],Nat.card Y<Nat.card X→
        MarkedC4.genRank H≤Nat.card Y/2) : MarkedC4.genRank G≤Nat.card X/2 := by
  letI : FaithfulSMul (Kernel S) ↥(Sᶜ) := kernel_complement_faithful S
  have hlt := degrees_lt S hS hC
  exact genRank_le_card_div S 2
    (hsmaller (Image S) S hlt.1) (hsmaller (Kernel S) ↥(Sᶜ) hlt.2)

theorem half_degree_of_intransitive {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hnot : ¬MulAction.IsPretransitive G X)
    (hsmaller : ∀(H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y],Nat.card Y<Nat.card X→
        MarkedC4.genRank H≤Nat.card Y/2) : MarkedC4.genRank G≤Nat.card X/2 := by
  obtain ⟨S,hS,hC⟩ := exists_nonempty_proper_invariant hnot
  exact half_degree_of_smaller_actions S hS hC hsmaller

end SymmetricSubgroupAsymptotics.PermutationOrdinaryGeneratorSplit
