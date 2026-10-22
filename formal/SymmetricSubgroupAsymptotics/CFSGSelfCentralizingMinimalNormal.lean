import SymmetricSubgroupAsymptotics.NormalSubgroupOuterEmbedding
import SymmetricSubgroupAsymptotics.OuterWreathPermutationCompression
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import Mathlib.GroupTheory.Commutator.Basic

/-! A self-centralizing actual minimal normal subgroup is contained in
every nontrivial normal subgroup. If it is simple, the actual ambient
quotient has order at most its outer automorphism group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGSelfCentralizingMinimalNormal

variable {G : Type} [Group G] [Finite G]

theorem le_every_nontrivial_normal
    (E : Subgroup G) (hE : IsMinimalNormalSubgroup E)
    (hC : Subgroup.centralizer (E : Set G) = ⊥)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : E ≤ N := by
  letI : E.Normal := hE.1
  by_cases hI : E ⊓ N = ⊥
  · have hc : ⁅N, E⁆ ≤ E ⊓ N :=
      le_inf (Subgroup.commutator_le_right N E) (Subgroup.commutator_le_left N E)
    rw [hI] at hc
    have hzero : ⁅N, E⁆ = ⊥ := le_bot_iff.mp hc
    have hNC : N ≤ Subgroup.centralizer (E : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero
    rw [hC] at hNC
    exact False.elim (hN (le_bot_iff.mp hNC))
  · have he : E ⊓ N = E := hE.2.2 (E ⊓ N) inferInstance hI inf_le_left
    exact he ▸ inf_le_right

theorem quotient_card_le_outer
    (E : Subgroup G) [E.Normal] [IsSimpleGroup E]
    (hnc : ¬ IsMulCommutative E)
    (hC : Subgroup.centralizer (E : Set G) = ⊥) :
    Nat.card (G ⧸ E) ≤ Nat.card (PrimitiveSocleRawStructure.Outer E) := by
  let hcenter := PrimitiveSocleRawStructure.centerless_of_nonabelian_simple E hnc
  let e : E ≃* (Fin 1 → E) := (MulEquiv.funUnique (Fin 1) E).symm
  exact OuterWreathPermutationCompression.oneFactor_card_le
    (NormalSubgroupOuterEmbedding.quotientEmbedding E hcenter e)
    (NormalSubgroupOuterEmbedding.quotientEmbedding_injective E hcenter e hC)

end SymmetricSubgroupAsymptotics.CFSGSelfCentralizingMinimalNormal
