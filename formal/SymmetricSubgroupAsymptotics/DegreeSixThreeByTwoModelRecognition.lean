import SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoProductRecognition
import SymmetricSubgroupAsymptotics.TwoTripleLiteralAffineSubgroupChart
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixPublishedClassification
import Mathlib.Tactic.IntervalCases

/-! Exact axes and full-wreath models, preserving the original subgroup
through its injective literal action and actual projection image. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoModelRecognition
open SemidirectProduct Non2UnipotentPrefixFiniteMenu

private theorem card_local : Nat.card TernaryLocalWreathNormalGenerators.Local = 6 := by
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd,Nat.card_zmod]
  rw [SemidirectProduct.card,h3,h2]

def localEquiv : TernaryLocalWreathNormalGenerators.Local ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective SixPointTernaryAxesNormalGenerators.localAction <|
    (Nat.bijective_iff_injective_and_card _).mpr
      ⟨SixPointTernaryAxesNormalGenerators.localAction_injective,
        card_local.trans DegreeSixThreeByTwoProductRecognition.card_s3.symm⟩

def axesEquiv : SixPointTernaryAxesNormalGenerators.Model ≃* DegreeSixS3Product.G :=
  localEquiv.prodCongr localEquiv

def wreathEquiv : TwoTripleFullUpperForcesFullWreath.Model ≃* DegreeSixS3Wreath.G :=
  SemidirectProduct.congr axesEquiv (MulEquiv.refl _) (by
    intro b
    rcases C2Wreath.cases b with rfl | rfl
    · ext x <;> rfl
    · ext x <;> simp [C2Wreath.swapAut_gen,axesEquiv] <;> rfl)

private def axesCoordinates : SixPointTernaryAxesNormalGenerators.Model ≃
    (ZMod 3 × Multiplicative (ZMod 2)) × (ZMod 3 × Multiplicative (ZMod 2)) where
  toFun g := ((g.1.left.toAdd,g.1.right),(g.2.left.toAdd,g.2.right))
  invFun p := (⟨Multiplicative.ofAdd p.1.1,p.1.2⟩,⟨Multiplicative.ofAdd p.2.1,p.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
local instance : Fintype SixPointTernaryAxesNormalGenerators.Model :=
  Fintype.ofEquiv _ axesCoordinates.symm

private theorem axes_faithful_receipt : ∀ g h : SixPointTernaryAxesNormalGenerators.Model,
    (∀ x : Fin 6, SixPointTernaryAxesNormalGenerators.literalAction g x =
      SixPointTernaryAxesNormalGenerators.literalAction h x) → g=h := by decide +kernel

theorem axes_action_injective : Function.Injective SixPointTernaryAxesNormalGenerators.literalAction := by
  intro g h he
  exact axes_faithful_receipt g h (fun x => Equiv.congr_fun he x)

private theorem order_cases (n : ℕ) (h36 : n ∣ 36) (h4 : 4 ∣ n) (h6 : 6 ∣ n) :
    n=12 ∨ n=36 := by
  have hn : n ≤ 36 := Nat.le_of_dvd (by decide) h36
  interval_cases n <;> norm_num at *

theorem axes_source {U : PreE7NonPairActionClass 6}
    (P : Subgroup (Equiv.Perm (Fin 6)))
    (E : preE7NonPairAction 6 U ≃* P)
    (hle : P ≤ SixPointTernaryAxesNormalGenerators.literalAction.range)
    (h4 : 4 ∣ Nat.card P) (h6 : 6 ∣ Nat.card P) :
    Nonempty (PublishedDegreeSixThreeByTwoAffineModel U) := by
  let K := P.comap SixPointTernaryAxesNormalGenerators.literalAction
  let pi : K →* P :=
    (SixPointTernaryAxesNormalGenerators.literalAction.comp K.subtype).codRestrict P (fun g => g.2)
  have hpi : Function.Bijective pi := by
    constructor
    · intro g h he
      exact Subtype.ext (axes_action_injective (congrArg Subtype.val he))
    · intro p
      obtain ⟨g,hg⟩ := hle p.2
      exact ⟨⟨g,by change SixPointTernaryAxesNormalGenerators.literalAction g ∈ P; rw [hg]; exact p.2⟩,
        Subtype.ext hg⟩
  let EK : P ≃* K := (MulEquiv.ofBijective pi hpi).symm
  have hcardK : Nat.card K = Nat.card P := (Nat.card_congr EK.toEquiv).symm
  have h36 : Nat.card K ∣ 36 := by
    have h := K.card_subgroup_dvd_card
    have hc : Nat.card SixPointTernaryAxesNormalGenerators.Model = 36 := by
      rw [Nat.card_prod,card_local]
    rwa [hc] at h
  rcases order_cases (Nat.card K) h36 (hcardK.symm ▸ h4) (hcardK.symm ▸ h6) with h12 | h36
  · let L := K.map axesEquiv.toMonoidHom
    let EL := K.equivMapOfInjective axesEquiv.toMonoidHom axesEquiv.injective
    have hL : Nat.card L = 12 := (Nat.card_congr EL.toEquiv).symm.trans h12
    exact ⟨.s3c2 (E.trans (EK.trans (EL.trans
      (DegreeSixThreeByTwoProductRecognition.subgroup_twelve L hL))))⟩
  · have hKtop : K = ⊤ := K.eq_top_of_card_eq (by
      rw [h36,Nat.card_prod,card_local])
    let ET : K ≃* SixPointTernaryAxesNormalGenerators.Model :=
      (MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv
    exact ⟨.s3Product { equiv := E.trans (EK.trans (ET.trans axesEquiv)) }⟩

def full_source {U : PreE7NonPairActionClass 6}
    (P : Subgroup (Equiv.Perm (Fin 6)))
    (E : preE7NonPairAction 6 U ≃* P)
    (heq : P = SixPairLocalWreathSocles.literalAction.range) :
    PublishedDegreeSixThreeByTwoAffineModel U :=
  .s3Wreath { equiv := E.trans ((MulEquiv.subgroupCongr heq).trans
    ((MonoidHom.ofInjective TwoTripleLiteralAffineSubgroupChart.literal_injective).symm.trans
      wreathEquiv)) }

end SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoModelRecognition
