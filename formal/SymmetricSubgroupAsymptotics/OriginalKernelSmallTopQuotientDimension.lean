import SymmetricSubgroupAsymptotics.OriginalKernelSmallTopQuotientCard

/-! The literal original retained section, rather than a cyclic ambient
row, can supply the dimension bound for a faithful eight-point comparator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {G B : Type} [Group G] [Finite G] [Group B]
  (pi : G →* B) (A : Rep.{0} (ZMod 2) B) [Finite A]
  (E : OriginalKernelModuleChart pi A) (N : Subgroup G) [N.Normal]

include E in
theorem quotient_card_le_eight_of_section_dimension
    (hdim : Module.finrank (ZMod 2) (E.sectionModule pi A N)≤2)
    (hsmall : Nat.card (G ⧸ (pi.ker ⊔ N))≤2) : Nat.card (G ⧸ N)≤8 := by
  letI : Finite (E.sectionModule pi A N) :=
    Finite.of_surjective (E.sectionProjection pi A N) (E.sectionProjection_surjective pi A N)
  let f := base pi N
  have hk : Nat.card f.ker≤4 := by
    rw [← Nat.card_congr (E.kernelEquiv pi A N).toEquiv]
    change Nat.card (E.sectionModule pi A N)≤4
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0<2) hdim).trans (by decide)
  have hp := f.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr (base_surjective pi N),
    Nat.card_congr Subgroup.topEquiv.toEquiv] at hp
  calc
    Nat.card (G ⧸ N)=Nat.card f.ker*Nat.card (G ⧸ (pi.ker ⊔ N)) := hp.symm
    _≤4*2 := Nat.mul_le_mul hk hsmall
    _=8 := by decide

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
