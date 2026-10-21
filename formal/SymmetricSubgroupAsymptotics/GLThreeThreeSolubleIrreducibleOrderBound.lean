import SymmetricSubgroupAsymptotics.IrreducibleMatrixScalarKernel
import SymmetricSubgroupAsymptotics.IrreducibleTernaryNormalThreeGroup
import SymmetricSubgroupAsymptotics.SolubleCentralNilpotentLayer
import SymmetricSubgroupAsymptotics.GLThreeThreeNormalNilpotentSplit
import SymmetricSubgroupAsymptotics.GLThreeThreeSingerNormalizer
import SymmetricSubgroupAsymptotics.NormalTwoGroupTernaryMonomialBound

/-! A finite soluble group with a faithful irreducible ternary
three-dimensional representation has order at most78. The proof uses
actual normal subgroups: a nonscalar normal two-group gives a monomial
action, while a normal subgroup of order13 gives the Singer normalizer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GLThreeThreeSolubleIrreducibleOrderBound
open StandardThreeDimensionalLinearGroups
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem card_le_of_normal_thirteen
    {G : Type} [Group G] [Finite G]
    (f : G →* GeneralThree 3) (hf : Function.Injective f)
    (P : Subgroup G) [P.Normal] (hP : Nat.card P=13) : Nat.card G≤78 := by
  let Q := P.map f
  have hQ : Nat.card Q=13 :=
    (Nat.card_congr (P.equivMapOfInjective f hf).toEquiv).symm.trans hP
  have hle := P.le_normalizer_map f
  have he := Nat.card_congr
    ((Subgroup.normalizer (P : Set G)).equivMapOfInjective f hf).toEquiv
  have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)
  have hn := he.le.trans (hc.trans
    (GLThreeThreeSingerNormalizer.order_thirteen_normalizer_card_le Q hQ))
  simpa only [Subgroup.normalizer_eq_top,Subgroup.card_top] using hn

theorem card_le
    {G V : Type} [Group G] [Finite G] [IsSolvable G]
    [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (rho : Representation (ZMod 3) G V) (hf : Function.Injective rho)
    (hrho : Representation.IsIrreducible rho)
    (hdim : Module.finrank (ZMod 3) V=3) : Nat.card G≤78 := by
  let b : Module.Basis (Fin 3) (ZMod 3) V :=
    Module.finBasisOfFinrankEq (ZMod 3) V hdim
  let f := IrreducibleMatrixScalarKernel.matrixMap rho b
  have hf' := IrreducibleMatrixScalarKernel.matrixMap_injective rho b hf
  let Z := IrreducibleMatrixScalarKernel.scalars rho b
  letI : Z.Normal := IrreducibleMatrixScalarKernel.scalars_normal rho b
  have hZ : Z≤Subgroup.center G :=
    IrreducibleMatrixScalarKernel.scalars_le_center rho b hf
  have hZproper : Z≠⊤ := IrreducibleMatrixScalarKernel.scalars_ne_top rho b hrho
  obtain ⟨B,hZB,hBnormal,hBnilpotent⟩ :=
    exists_normal_nilpotent_strictly_above_central Z hZ hZproper
  letI : B.Normal := hBnormal
  letI : Group.IsNilpotent B := hBnilpotent
  have hV : 3∣Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V),Nat.card_zmod,hdim]
    decide
  have hno3 (N : Subgroup G) (hNnormal : N.Normal) (hN : IsPGroup 3 N) : N=⊥ := by
    letI : N.Normal := hNnormal
    exact IrreducibleTernaryNormalThreeGroup.eq_bot_of_faithful_irreducible
      rho N hrho hf hN hV
  rcases GLThreeThreeNormalNilpotentSplit.two_group_or_normal_thirteen f hf' hno3 B
      with hBtwo|⟨P,hPnormal,hPcard⟩
  · have hnonscalar : ∃ n : B,¬∃ a : ZMod 3,
        rho n.val=a • (1 : Module.End (ZMod 3) V) := by
      obtain ⟨g,hgB,hgZ⟩ := SetLike.exists_of_lt hZB
      refine ⟨⟨g,hgB⟩,?_⟩
      intro hg
      exact hgZ ((IrreducibleMatrixScalarKernel.mem_scalars_iff rho b g).mpr hg)
    exact (NormalTwoGroupTernaryMonomialBound.card_le_fortyEight
      rho hf hrho hdim B hBtwo hnonscalar).trans (by decide)
  · letI : P.Normal := hPnormal
    exact card_le_of_normal_thirteen f hf' P hPcard

theorem card_le_of_prime_eq_three
    {p : ℕ} [Fact p.Prime] (hp : p=3)
    {G V : Type} [Group G] [Finite G] [IsSolvable G]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (rho : Representation (ZMod p) G V) (hf : Function.Injective rho)
    (hrho : Representation.IsIrreducible rho)
    (hdim : Module.finrank (ZMod p) V=3) : Nat.card G≤78 := by
  subst p
  exact card_le rho hf hrho hdim

end SymmetricSubgroupAsymptotics.GLThreeThreeSolubleIrreducibleOrderBound
