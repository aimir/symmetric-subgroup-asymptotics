import SymmetricSubgroupAsymptotics.CFSGNormalSubgroupSimpleProduct
import Mathlib.GroupTheory.IsSubnormal

/-! Subnormal subgroups of a finite product of nonabelian simple groups
are literal coordinate products. Normality is proved along the given
subnormal chain, not imported as a structural or classification input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSubnormalSimpleProduct
open CFSGNormalSubgroupSimpleProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
    (S : I → Type*) [∀ i, Group (S i)] [∀ i, IsSimpleGroup (S i)]
    (hn : ∀ i, ¬ IsMulCommutative (S i))
include hn

theorem normal_of_subnormal (N : Subgroup (∀ i, S i)) (hN : N.IsSubnormal) : N.Normal := by
  classical
  induction hN with
  | top => infer_instance
  | step N K hNK hK hnormal ih =>
    letI : K.Normal := ih
    have hmap (i : I) : (K.map (Pi.evalMonoidHom S i)).Normal :=
      Subgroup.Normal.map inferInstance _ (fun a => ⟨Pi.mulSingle i a, Pi.mulSingle_eq_same i a⟩)
    refine ⟨?_⟩
    intro n hmem g
    let k : ∀ i, S i := fun i => if K.map (Pi.evalMonoidHom S i) = ⊤ then g i else 1
    have hk : k ∈ K := by
      have hi (i : I) : Pi.mulSingle i (k i) ∈ K := by
        by_cases ht : K.map (Pi.evalMonoidHom S i) = ⊤
        · have hgi : g i ∈ K.map (Pi.evalMonoidHom S i) := by rw [ht]; trivial
          obtain ⟨x, hx, hxi⟩ := hgi
          have he : x i = g i := hxi
          simpa only [k, if_pos ht, he] using
            coordinate_mem_of_normal_simple S K hn ⟨x, hx⟩ i
        · simpa only [k, if_neg ht, Pi.mulSingle_one] using K.one_mem
      rw [← Finset.noncommProd_mulSingle k]
      exact K.noncommProd_mem _ (fun i _ => hi i)
    have he : g * n * g⁻¹ = k * n * k⁻¹ := by
      funext i
      by_cases ht : K.map (Pi.evalMonoidHom S i) = ⊤
      · simp only [Pi.mul_apply, Pi.inv_apply, k, if_pos ht]
      · have hb : K.map (Pi.evalMonoidHom S i) = ⊥ :=
          ((hmap i).eq_bot_or_eq_top).resolve_right ht
        have hz : n i = 1 := by
          have hm : n i ∈ K.map (Pi.evalMonoidHom S i) := ⟨n, hNK hmem, rfl⟩
          rw [hb] at hm
          exact Subgroup.mem_bot.mp hm
        simp only [Pi.mul_apply, Pi.inv_apply, hz, mul_one, mul_inv_cancel]
    rw [he]
    exact (Subgroup.normal_subgroupOf_iff hNK).mp hnormal n k hmem hk

theorem subnormal_eq_coordinate_product (N : Subgroup (∀ i, S i)) (hN : N.IsSubnormal) :
    N = Subgroup.pi Set.univ (fun i => N.map (Pi.evalMonoidHom S i)) := by
  letI := normal_of_subnormal S hn N hN
  exact normal_eq_coordinate_product S hn N

end SymmetricSubgroupAsymptotics.CFSGSubnormalSimpleProduct
