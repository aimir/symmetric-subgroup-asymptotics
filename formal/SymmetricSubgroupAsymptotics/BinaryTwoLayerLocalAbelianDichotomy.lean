import SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalClassTwo
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! A local abelian subgroup of the physical pair stabilizer is cyclic
or is killed by two. Only a selected 24² permutation calculation is used;
there is no subgroup enumeration. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalAbelianDichotomy
open BinaryTwoLayerLocalClassTwo

private theorem commuting_nonsquare_rows :
    ∀ a b : Equiv.Perm Points,PairRows a → PairRows b →
      a*b=b*a → a^2≠1 → ∃ k : Fin 4,b=a^k.val := by
  unfold PairRows
  decide +kernel

 theorem cyclic_or_square_one (L : Subgroup (Equiv.Perm Points))
    (hp : ∀ a : L,Preserves a.val) (hc : ∀ a b : L,a*b=b*a) :
    IsCyclic L ∨ ∀ a : L,a^2=1 := by
  classical
  by_cases hs : ∀ a : L,a^2=1
  · exact Or.inr hs
  · push_neg at hs
    obtain ⟨a,ha⟩ := hs
    apply Or.inl
    apply isCyclic_iff_exists_zpowers_eq_top.mpr
    refine ⟨a,top_unique ?_⟩
    intro b _
    have hab : a.val*b.val=b.val*a.val := congrArg Subtype.val (hc a b)
    have hne : a.val^2≠1 := by
      intro h
      exact ha (Subtype.ext h)
    obtain ⟨k,hk⟩ := commuting_nonsquare_rows a.val b.val
      ((preserves_iff_pairRows a.val).mp (hp a))
      ((preserves_iff_pairRows b.val).mp (hp b)) hab hne
    have hb : b=a^k.val := Subtype.ext hk
    rw [hb]
    exact Subgroup.npow_mem_zpowers a k.val

end SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalAbelianDichotomy
