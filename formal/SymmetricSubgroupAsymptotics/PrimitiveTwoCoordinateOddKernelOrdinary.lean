import SymmetricSubgroupAsymptotics.PrimitiveNormalDegreeDivisibility
import SymmetricSubgroupAsymptotics.TwoCoordinateAxisOrdinaryGenerators

/-! An odd coordinate kernel in an actual two-coordinate subdirect over
an even-degree primitive component is trivial. This retains the actual
correlated subdirect and its original normal quotient. The oddness premise
is structural, to be supplied by an actual original point stabilizer. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveTwoCoordinateOddKernelOrdinary

variable {N L X : Type} [Group N] [Finite N] [Group L] [Finite L]
    [Finite X] [Nonempty X] [MulAction L X] [FaithfulSMul L X]
    [MulAction.IsPreprimitive L X]

omit [Finite N] in
theorem coordinate_injective (f g : N →* L) (hg : Function.Surjective g)
    (hjoint : Function.Injective (fun x : N => (f x,g x)))
    (heven : 2 ∣ Nat.card X) (hodd : ¬2 ∣ Nat.card f.ker) :
    Function.Injective f := by
  let A : Subgroup L := f.ker.map g
  letI : A.Normal := Subgroup.Normal.map inferInstance g hg
  have hdiv : Nat.card A ∣ Nat.card f.ker :=
    Subgroup.card_dvd_of_surjective (g.subgroupMap f.ker) (g.subgroupMap_surjective f.ker)
  have hA : A = ⊥ :=
    PrimitiveNormalDegreeDivisibility.eq_bot_of_degree_divisor_not_dvd_card
      (X := X) A 2 heven (fun h => hodd (h.trans hdiv))
  apply f.ker_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  have hgx : g x ∈ A := ⟨x,hx,rfl⟩
  rw [hA,Subgroup.mem_bot] at hgx
  have hfx : f x = 1 := hx
  have hx1 : x = 1 := hjoint (by
    change (f x,g x) = (f 1,g 1)
    rw [hfx,hgx,map_one,map_one])
  exact Subgroup.mem_bot.mpr hx1


theorem genRank_le_local_add_quotient
    {G L X : Type} [Group G] [Finite G] [Group L] [Finite L]
    [Finite X] [Nonempty X] [MulAction L X] [FaithfulSMul L X]
    [MulAction.IsPreprimitive L X]
    (N : Subgroup G) [N.Normal] (f g : N →* L)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hjoint : Function.Injective (fun x : N => (f x,g x)))
    (heven : 2 ∣ Nat.card X) (hodd : ¬2 ∣ Nat.card f.ker) :
    MarkedC4.genRank G ≤ MarkedC4.genRank L + MarkedC4.genRank (G ⧸ N) := by
  let e : N ≃* L := MulEquiv.ofBijective f
    ⟨coordinate_injective (X := X) f g hg hjoint heven hodd,hf⟩
  have hh := MarkedC4.genRank_le_of_normal N
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e] at hh
  exact hh

end SymmetricSubgroupAsymptotics.PrimitiveTwoCoordinateOddKernelOrdinary
