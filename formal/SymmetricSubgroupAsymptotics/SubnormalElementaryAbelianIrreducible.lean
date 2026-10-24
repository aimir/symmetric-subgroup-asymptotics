import Mathlib.GroupTheory.IsSubnormal
import Mathlib.GroupTheory.Commutator.Basic

/-! A subnormal subgroup that acts irreducibly and nontrivially by
conjugation on a normal subgroup must contain it. The group-theoretic
statement is stronger than the elementary-abelian application: no field,
splitting, or coprime-order assumption is needed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SubnormalElementaryAbelianIrreducible

variable {G : Type*} [Group G]

/-- Irreducibility is tested on actual subgroups of the original normal
subgroup and actual conjugation by the specified subgroup. -/
def IrreducibleConjugation (N V : Subgroup G) : Prop :=
  ∀ W : Subgroup G, W ≤ V → N ≤ Subgroup.normalizer (W : Set G) →
    W = ⊥ ∨ W = V

/-- Passing upwards in the same ambient group preserves this actual
conjugation irreducibility. -/
theorem IrreducibleConjugation.mono {N H V : Subgroup G}
    (h : IrreducibleConjugation N V) (hNH : N ≤ H) :
    IrreducibleConjugation H V :=
  fun W hWV hHW => h W hWV (hNH.trans hHW)

/-- The subnormal-chain induction retains the original ambient normal
subgroup. At each step its intersection with the lower subgroup is
invariant; a trivial intersection forces the two subgroups to commute. -/
theorem le_of_subnormal_irreducible_noncentral
    (V : Subgroup G) [V.Normal] (N : Subgroup G) (hN : N.IsSubnormal)
    (hirr : IrreducibleConjugation N V)
    (hnoncentral : ¬ N ≤ Subgroup.centralizer (V : Set G)) : V ≤ N := by
  revert hirr hnoncentral
  induction hN with
  | top =>
    intro _ _
    exact le_top
  | step H K hHK hK hnormal ih =>
    intro hirr hnoncentral
    have hVK : V ≤ K := ih (hirr.mono hHK)
      (fun hcentral => hnoncentral (hHK.trans hcentral))
    have hHnormalizes : H ≤ Subgroup.normalizer ((H ⊓ V : Subgroup G) : Set G) :=
      (le_inf H.le_normalizer Subgroup.le_normalizer_of_normal).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    rcases hirr (H ⊓ V) inf_le_right hHnormalizes with hzero | hfull
    · exfalso
      apply hnoncentral
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      have hVH : V ≤ Subgroup.normalizer (H : Set G) :=
        hVK.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hnormal)
      have hleft : ⁅H, V⁆ ≤ H :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp hVH
      have hright : ⁅H, V⁆ ≤ V :=
        Subgroup.le_normalizer_iff_commutator_le_right.mp
          (show H ≤ Subgroup.normalizer (V : Set G) from
            Subgroup.le_normalizer_of_normal)
      exact le_bot_iff.mp ((le_inf hleft hright).trans_eq hzero)
    · rw [← hfull]
      exact inf_le_left

end SymmetricSubgroupAsymptotics.SubnormalElementaryAbelianIrreducible
