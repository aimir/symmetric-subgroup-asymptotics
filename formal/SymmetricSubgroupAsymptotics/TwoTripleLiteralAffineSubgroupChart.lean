import SymmetricSubgroupAsymptotics.TwoTripleSignedAffineCoordinates
import SymmetricSubgroupAsymptotics.TwoTripleProperUpperModelCovers

/-! A literal two-triple action has its actual affine subgroup chart.
No subgroup census, pure complement, or full translation kernel is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwoTripleLiteralAffineSubgroupChart
open TwoTripleSignedAffineCoordinates
open TwoTripleSignedUpperLinearAction

private def coordinates : Wreath ≃
    ((ZMod 3 × Binary) × (ZMod 3 × Binary)) × Binary where
  toFun g := (((g.left.1.left.toAdd,g.left.1.right),
    (g.left.2.left.toAdd,g.left.2.right)),g.right)
  invFun p := ⟨(⟨Multiplicative.ofAdd p.1.1.1,p.1.1.2⟩,
    ⟨Multiplicative.ofAdd p.1.2.1,p.1.2.2⟩),p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
local instance literalAffineWreathFintype : Fintype Wreath :=
  Fintype.ofEquiv _ coordinates.symm

private theorem faithful_receipt : ∀ g h : Wreath,
    (∀ x : Fin 6, SixPairLocalWreathSocles.literalAction g x=
      SixPairLocalWreathSocles.literalAction h x) → g=h := by decide +kernel

theorem literal_injective : Function.Injective SixPairLocalWreathSocles.literalAction := by
  intro g h he
  exact faithful_receipt g h (fun x => Equiv.congr_fun he x)

variable (P : Subgroup (Equiv.Perm (Fin 6)))
    (hle : P≤SixPairLocalWreathSocles.literalAction.range)

abbrev pullback : Subgroup Wreath := P.comap SixPairLocalWreathSocles.literalAction
abbrev affineSubgroup : Subgroup Affine := (pullback P).map equiv.toMonoidHom

def literalMap : pullback P →* P :=
  (SixPairLocalWreathSocles.literalAction.comp (pullback P).subtype).codRestrict P
    (fun g => g.property)

include hle in
theorem literalMap_bijective : Function.Bijective (literalMap P) := by
  constructor
  · intro g h he
    exact Subtype.ext (literal_injective (congrArg Subtype.val he))
  · intro p
    obtain ⟨g,hg⟩ := hle p.property
    exact ⟨⟨g,by change SixPairLocalWreathSocles.literalAction g∈P; rw [hg]; exact p.property⟩,
      Subtype.ext hg⟩

include hle in
def groupChart : P ≃* affineSubgroup P :=
  (MulEquiv.ofBijective (literalMap P) (literalMap_bijective P hle)).symm.trans
    (equiv.subgroupMap (pullback P))

include hle in
/-- Actual transitivity supplies the block-exchanging upper lift. -/
theorem upper_swap [MulAction.IsPretransitive P (Fin 6)] :
    ∃ u : LinearSemidirectSubgroupKernelChart.Image linearAction (affineSubgroup P),
      (u : Upper).right=C2Wreath.gen := by
  obtain ⟨p,hp⟩ := MulAction.exists_smul_eq P (0 : Fin 6) 1
  obtain ⟨g,hg⟩ := hle p.property
  have hgmem : g∈pullback P := by
    change SixPairLocalWreathSocles.literalAction g∈P
    rw [hg]
    exact p.property
  let k : affineSubgroup P := ⟨equiv g,⟨g,hgmem,rfl⟩⟩
  let u := LinearSemidirectSubgroupKernelChart.projection linearAction (affineSubgroup P) k
  refine ⟨⟨u,⟨k,rfl⟩⟩,?_⟩
  exact TwoTripleProperUpperModelCovers.swap_of_point g (by rw [hg]; exact hp)

end SymmetricSubgroupAsymptotics.TwoTripleLiteralAffineSubgroupChart
