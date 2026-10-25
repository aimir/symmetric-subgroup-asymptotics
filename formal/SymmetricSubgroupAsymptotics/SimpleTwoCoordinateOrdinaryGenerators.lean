import SymmetricSubgroupAsymptotics.TwoCoordinateAxisOrdinaryGenerators
import Mathlib.GroupTheory.Subgroup.Simple

/-! A literal two-coordinate subdirect over a simple local group has
an injective coordinate or a full actual axis. With an actual coordinate
swapper, either case pays the rank of one local group above the original
normal quotient. Arbitrary diagonal correlations are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SimpleTwoCoordinateOrdinaryGenerators

theorem injective_or_full_axis
    {N L : Type} [Group N] [Group L] [IsSimpleGroup L]
    (f g : N →* L) (hf : Function.Surjective f)
    (hjoint : Function.Injective (fun x : N => (f x,g x))) :
    Function.Injective g ∨ Function.Surjective (f.comp g.ker.subtype) := by
  let A : Subgroup L := g.ker.map f
  letI : A.Normal := Subgroup.Normal.map inferInstance f hf
  rcases (inferInstance : A.Normal).eq_bot_or_eq_top with hzero | hfull
  · apply Or.inl
    apply g.ker_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    have hfx : f x ∈ A := ⟨x,hx,rfl⟩
    rw [hzero,Subgroup.mem_bot] at hfx
    have hgx : g x = 1 := hx
    have hx1 : x = 1 := hjoint (by
      change (f x,g x) = (f 1,g 1)
      rw [hfx,hgx,map_one,map_one])
    exact Subgroup.mem_bot.mpr hx1
  · apply Or.inr
    intro l
    have hl : l ∈ A := by rw [hfull]; trivial
    obtain ⟨x,hx,hfx⟩ := hl
    exact ⟨⟨x,hx⟩,hfx⟩

theorem genRank_le_local_add_quotient
    {G L : Type} [Group G] [Finite G] [Group L] [Finite L] [IsSimpleGroup L]
    (N : Subgroup G) [N.Normal] (f g : N →* L)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hjoint : Function.Injective (fun x : N => (f x,g x)))
    (h : G) (alpha : MulAut L)
    (hconj : ∀ x : N, f ((MulAut.conjNormal h) x) = alpha (g x)) :
    MarkedC4.genRank G ≤ MarkedC4.genRank L + MarkedC4.genRank (G ⧸ N) := by
  rcases injective_or_full_axis f g hf hjoint with hinj | haxis
  · let e : N ≃* L := MulEquiv.ofBijective g ⟨hinj,hg⟩
    have hh := MarkedC4.genRank_le_of_normal N
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e] at hh
    exact hh
  · exact TwoCoordinateAxisOrdinaryGenerators.genRank_le_local_add_quotient
      N f g hjoint haxis h alpha hconj

end SymmetricSubgroupAsymptotics.SimpleTwoCoordinateOrdinaryGenerators
