import SymmetricSubgroupAsymptotics.PerfectSubdirect
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Normal subgroups of a product of nonabelian simple groups retain
whole original factors. A surjective coordinate is isolated by actual
commutators, then perfectness supplies its entire coordinate subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGNormalSubgroupSimpleProduct
variable {I : Type*} [DecidableEq I] (S : I → Type*) [∀ i, Group (S i)]

 theorem coordinate_mem_of_normal_surjective (N : Subgroup (∀ i, S i)) [N.Normal]
    (i : I) [Group.IsPerfect (S i)]
    (hs : Function.Surjective ((Pi.evalMonoidHom S i).comp N.subtype)) (a : S i) :
    Pi.mulSingle i a ∈ N := by
  classical
  let c : S i →* ∀ i, S i := MonoidHom.mulSingle S i
  have h : commutator (S i) ≤ N.comap c := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    obtain ⟨n, hn⟩ := hs y
    have hm : ⁅c x, n.val⁆ ∈ N :=
      Subgroup.commutator_le_right ⊤ N (Subgroup.commutator_mem_commutator (by trivial) n.property)
    have he : c ⁅x, y⁆ = ⁅c x, n.val⁆ := by
      funext j
      by_cases hj : j = i
      · subst j
        have hh : n.val i = y := hn
        simp only [c, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same,
          commutatorElement_def, Pi.mul_apply, Pi.inv_apply, hh]
      · simp [c, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj,
          commutatorElement_def]
    change c ⁅x, y⁆ ∈ N
    rw [he]
    exact hm
  rw [Group.IsPerfect.commutator_eq_top] at h
  exact h (by trivial)

 theorem coordinate_mem_of_normal_simple (N : Subgroup (∀ i, S i)) [N.Normal]
    [∀ i, IsSimpleGroup (S i)] (hn : ∀ i, ¬ IsMulCommutative (S i))
    (g : N) (i : I) : Pi.mulSingle i (g.val i) ∈ N := by
  classical
  let f := (Pi.evalMonoidHom S i).comp N.subtype
  have hsurj : Function.Surjective (Pi.evalMonoidHom S i) := by
    intro x
    exact ⟨Pi.mulSingle i x, Pi.mulSingle_eq_same i x⟩
  have hr : f.range = N.map (Pi.evalMonoidHom S i) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hnormal : f.range.Normal := by
    rw [hr]
    exact Subgroup.Normal.map inferInstance _ hsurj
  rcases hnormal.eq_bot_or_eq_top with hb | ht
  · have hz : g.val i = 1 := by
      have hg : f g ∈ f.range := ⟨g, rfl⟩
      rw [hb] at hg
      exact Subgroup.mem_bot.mp hg
    simpa only [hz, Pi.mulSingle_one] using N.one_mem
  · letI : Group.IsPerfect (S i) := simple_perfect_of_nonabelian (hn i)
    exact coordinate_mem_of_normal_surjective S N i (MonoidHom.range_eq_top.mp ht) (g.val i)

 theorem normal_eq_coordinate_product [Fintype I]
    [∀ i, IsSimpleGroup (S i)] (hn : ∀ i, ¬ IsMulCommutative (S i))
    (N : Subgroup (∀ i, S i)) [N.Normal] :
    N = Subgroup.pi Set.univ (fun i => N.map (Pi.evalMonoidHom S i)) := by
  ext g
  constructor
  · intro hg i _
    exact ⟨g, hg, rfl⟩
  · intro hg
    have hi (i : I) : Pi.mulSingle i (g i) ∈ N := by
      obtain ⟨x, hx, hxi⟩ := hg i (by trivial)
      have h := coordinate_mem_of_normal_simple S N hn ⟨x, hx⟩ i
      have he : x i = g i := hxi
      simpa only [he] using h
    rw [← Finset.noncommProd_mulSingle g]
    exact N.noncommProd_mem _ (fun i _ => hi i)

end SymmetricSubgroupAsymptotics.CFSGNormalSubgroupSimpleProduct
