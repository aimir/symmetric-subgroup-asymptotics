import SymmetricSubgroupAsymptotics.CFSGNormalizerTranspositionClasses
import SymmetricSubgroupAsymptotics.CFSGNormalTwoGroupDisjointThreeCycle

/-! A permutation two-group preserves every transposition class of its
normalizer that has at least three points. Displacing such a class gives
an actual normalizing three-cycle with disjoint conjugate support. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGNormalTwoGroupTranspositionClasses
open Equiv Equiv.Perm CFSGNormalizerTranspositionClasses

theorem preserves_large_class {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hP : IsPGroup 2 P) (x : X)
    (hsize : 2 < (pointClass (Subgroup.normalizer (P : Set (Perm X))) x).ncard)
    (g : Perm X) (hg : g ∈ P) :
    g '' pointClass (Subgroup.normalizer (P : Set (Perm X))) x =
      pointClass (Subgroup.normalizer (P : Set (Perm X))) x := by
  let N := Subgroup.normalizer (P : Set (Perm X))
  have hgN : g ∈ N := Subgroup.le_normalizer hg
  have hrel : related N x (g x) := by
    by_contra hn
    have hclasses : Disjoint (pointClass N x) (pointClass N (g x)) := by
      rcases classes_eq_or_disjoint N x (g x) with he | hd
      · have hm : g x ∈ pointClass N (g x) := related_refl N (g x)
        rw [← he] at hm
        exact False.elim (hn hm)
      · exact hd
    have hthree : 2 < (pointClass N x).ncard := hsize
    rw [Set.two_lt_ncard_iff] at hthree
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hthree
    let u : Perm X := Equiv.swap a b * Equiv.swap a c
    have hu3 : IsThreeCycle u := isThreeCycle_swap_mul_swap_same hab hac hbc
    have huN : u ∈ N := N.mul_mem (sameClass_swap_mem N ha hb) (sameClass_swap_mem N ha hc)
    have hsupport : (u.support : Set X) ⊆ pointClass N x := by
      intro y hy
      have hbound : u.support ⊆ ({a, b, c} : Finset X) := by
        calc
          u.support ≤ (Equiv.swap a b).support ⊔ (Equiv.swap a c).support :=
            support_mul_le _ _
          _ = ({a, b, c} : Finset X) := by
            rw [support_swap hab, support_swap hac]
            ext z
            change z ∈ ({a, b} : Finset X) ∪ {a, c} ↔ z ∈ ({a, b, c} : Finset X)
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
            tauto
      have hh : y ∈ ({a, b, c} : Finset X) := hbound hy
      rcases Finset.mem_insert.mp hh with rfl | hh
      · exact ha
      · rcases Finset.mem_insert.mp hh with rfl | hh
        · exact hb
        · exact (Finset.mem_singleton.mp hh) ▸ hc
    have hd : Perm.Disjoint u (g * u * g⁻¹) := by
      apply disjoint_iff_disjoint_support.mpr
      apply Finset.disjoint_left.mpr
      intro y hy hy'
      have hyC := hsupport hy
      rw [support_conj] at hy'
      obtain ⟨z, hz, he⟩ := Finset.mem_map.mp hy'
      have hyGC : y ∈ g '' pointClass N x := ⟨z, hsupport hz, he⟩
      rw [pointClass_image N g hgN x] at hyGC
      exact Set.disjoint_left.mp hclasses hyC hyGC
    exact CFSGNormalTwoGroupDisjointThreeCycle.impossible P hP g u hg huN hu3 hd
  rw [pointClass_image N g hgN x]
  ext y
  exact ⟨fun hy => related_trans N hrel hy,
    fun hy => related_trans N (related_symm N hrel) hy⟩

end SymmetricSubgroupAsymptotics.CFSGNormalTwoGroupTranspositionClasses
