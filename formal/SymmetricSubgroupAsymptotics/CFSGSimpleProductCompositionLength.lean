import SymmetricSubgroupAsymptotics.CFSGSubnormalSimpleProduct
import SymmetricSubgroupAsymptotics.SubnormalCompositionRefinement
import Mathlib.Data.Finset.Card

/-! Any actual composition series of a finite product of nonabelian
simple groups has at most one step per original coordinate. This bounds
all original subnormal chains, rather than choosing a convenient series. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSimpleProductCompositionLength
open CFSGNormalSubgroupSimpleProduct CFSGSubnormalSimpleProduct
variable {I : Type} [Fintype I] [DecidableEq I]
    (S : I → Type) [∀ i, Group (S i)] [∀ i, IsSimpleGroup (S i)]
    (hn : ∀ i, ¬ IsMulCommutative (S i))

noncomputable def support (N : Subgroup (∀ i, S i)) : Finset I :=
  by
    classical
    exact Finset.univ.filter fun i => N.map (Pi.evalMonoidHom S i) = ⊤

@[simp] theorem mem_support (N : Subgroup (∀ i, S i)) (i : I) :
    i ∈ support S N ↔ N.map (Pi.evalMonoidHom S i) = ⊤ := by simp [support]

theorem support_mono {N M : Subgroup (∀ i, S i)} (h : N ≤ M) :
    support S N ⊆ support S M := by
  intro i hi
  rw [mem_support] at hi ⊢
  exact top_unique (hi ▸ Subgroup.map_mono h)

include hn in
theorem support_injective {N M : Subgroup (∀ i, S i)} [N.Normal] [M.Normal]
    (h : support S N = support S M) : N = M := by
  have hsurj (i : I) : Function.Surjective (Pi.evalMonoidHom S i) :=
    fun a => ⟨Pi.mulSingle i a, Pi.mulSingle_eq_same i a⟩
  have hmap (i : I) : N.map (Pi.evalMonoidHom S i) = M.map (Pi.evalMonoidHom S i) := by
    letI : (N.map (Pi.evalMonoidHom S i)).Normal := Subgroup.Normal.map inferInstance _ (hsurj i)
    letI : (M.map (Pi.evalMonoidHom S i)).Normal := Subgroup.Normal.map inferInstance _ (hsurj i)
    have ht : N.map (Pi.evalMonoidHom S i) = ⊤ ↔ M.map (Pi.evalMonoidHom S i) = ⊤ := by
      rw [← mem_support, ← mem_support, h]
    rcases (inferInstance : (N.map (Pi.evalMonoidHom S i)).Normal).eq_bot_or_eq_top with hb | hb
    · rcases (inferInstance : (M.map (Pi.evalMonoidHom S i)).Normal).eq_bot_or_eq_top with hc | hc
      · exact hb.trans hc.symm
      · exact (ht.mpr hc).trans hc.symm
    · exact hb.trans (ht.mp hb).symm
  rw [normal_eq_coordinate_product S hn N, normal_eq_coordinate_product S hn M]
  simp_rw [hmap]

include hn in
theorem support_strict {N M : Subgroup (∀ i, S i)} (hN : N.IsSubnormal)
    (hM : M.IsSubnormal) (h : N < M) : support S N ⊂ support S M := by
  letI := normal_of_subnormal S hn N hN
  letI := normal_of_subnormal S hn M hM
  exact Finset.ssubset_iff_subset_ne.mpr ⟨support_mono S h.le,
    fun he => h.ne (support_injective S hn he)⟩

include hn in
theorem length_le_card_factors (s : SubnormalCompositionSeries (∀ i, S i)) :
    s.chain.length ≤ Fintype.card I := by
  have hb (j : Fin (s.chain.length + 1)) :
      j.val ≤ (support S (s.chain j).val).card := by
    induction j using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hstep := (s.chain.step j).1
      have hc := Finset.card_lt_card (support_strict S hn
        (s.chain j.castSucc).property (s.chain j.succ).property hstep)
      change j.val + 1 ≤ _
      exact Nat.succ_le_of_lt (lt_of_le_of_lt (by simpa only [Fin.val_castSucc] using ih) hc)
  exact (hb (Fin.last _)).trans (Finset.card_le_univ _)

end SymmetricSubgroupAsymptotics.CFSGSimpleProductCompositionLength
