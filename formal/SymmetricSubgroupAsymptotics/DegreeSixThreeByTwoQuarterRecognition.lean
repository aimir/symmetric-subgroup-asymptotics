import SymmetricSubgroupAsymptotics.SixPointTernaryQuarterTurnNormalGenerators
import SymmetricSubgroupAsymptotics.TernaryPlaneDihedralAffineNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixPublishedClassification

/-! Exact recognition of the quarter-turn branch of a two-triple action.
A transitive subgroup projecting onto C₄ has nonzero ternary kernel.
The quarter-turn makes that kernel the full ternary plane, so the subgroup
is the whole displayed affine group. Offset lifts are never assumed pure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoQuarterRecognition
open SemidirectProduct

private def coordinates : SixPointTernaryQuarterTurnNormalGenerators.Model ≃ SixPointTernaryQuarterTurnNormalGenerators.Vector × SixPointTernaryQuarterTurnNormalGenerators.Upper where
  toFun g := (g.left.toAdd,g.right)
  invFun p := ⟨Multiplicative.ofAdd p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
local instance : Fintype SixPointTernaryQuarterTurnNormalGenerators.Model := Fintype.ofEquiv _ coordinates.symm

private theorem inverse_action : ∀ (v : SixPointTernaryQuarterTurnNormalGenerators.Vector),
    LinearSemidirectCoprimeSocleBounds.linearAction SixPointTernaryQuarterTurnNormalGenerators.linearAction SixPointTernaryQuarterTurnNormalGenerators.gen⁻¹
      (Multiplicative.ofAdd v) = Multiplicative.ofAdd (TernaryPlaneDihedralAffineNormalGenerators.quarterTurn v) := by
  decide +kernel

private theorem generator_pow : ∀ c : SixPointTernaryQuarterTurnNormalGenerators.Upper, SixPointTernaryQuarterTurnNormalGenerators.gen ^ c.toAdd.val = c := by
  decide +kernel

private theorem faithful_receipt : ∀ g h : SixPointTernaryQuarterTurnNormalGenerators.Model,
    (∀ x : Fin 6, SixPointTernaryQuarterTurnNormalGenerators.literalAction g x = SixPointTernaryQuarterTurnNormalGenerators.literalAction h x) → g = h := by
  decide +kernel

theorem action_injective : Function.Injective SixPointTernaryQuarterTurnNormalGenerators.literalAction := by
  intro g h he
  exact faithful_receipt g h (fun x => Equiv.congr_fun he x)

theorem full_of_nonzero_kernel (K : Subgroup SixPointTernaryQuarterTurnNormalGenerators.Model)
    (lift : SixPointTernaryQuarterTurnNormalGenerators.Model) (hlift : lift ∈ K) (hgen : lift.right = SixPointTernaryQuarterTurnNormalGenerators.gen)
    (hne : ∃ g : SixPointTernaryQuarterTurnNormalGenerators.Model, g ∈ K ∧ g.right = 1 ∧ g ≠ 1) : K = ⊤ := by
  let A := LinearSemidirectSubgroupKernelChart.translationSpace SixPointTernaryQuarterTurnNormalGenerators.linearAction K
  have hAne : A ≠ ⊥ := by
    obtain ⟨g,hg,hgR,hg1⟩ := hne
    have hgA : g.left.toAdd ∈ A := by
      change inl g.left ∈ K
      have he : (inl g.left : SixPointTernaryQuarterTurnNormalGenerators.Model) = g := by
        apply SemidirectProduct.ext
        · rfl
        · exact hgR.symm
      rwa [he]
    intro hbot
    rw [hbot] at hgA
    have hgL : g.left = 1 := Multiplicative.toAdd.injective
      ((Submodule.mem_bot (R := ZMod 3)).mp hgA)
    exact hg1 (SemidirectProduct.ext hgL hgR)
  have hJ (v : SixPointTernaryQuarterTurnNormalGenerators.Vector) (hv : v ∈ A) : TernaryPlaneDihedralAffineNormalGenerators.quarterTurn v ∈ A := by
    change inl (Multiplicative.ofAdd v) ∈ K at hv
    have h := K.mul_mem (K.mul_mem (K.inv_mem hlift) hv) hlift
    change inl (Multiplicative.ofAdd (TernaryPlaneDihedralAffineNormalGenerators.quarterTurn v)) ∈ K
    have he : lift⁻¹ * inl (Multiplicative.ofAdd v) * lift =
        (inl (Multiplicative.ofAdd (TernaryPlaneDihedralAffineNormalGenerators.quarterTurn v)) : SixPointTernaryQuarterTurnNormalGenerators.Model) := by
      have hc := LinearSemidirectCoprimeSocleBounds.conjugate_translation
        SixPointTernaryQuarterTurnNormalGenerators.linearAction lift⁻¹ (Multiplicative.ofAdd v)
      simpa only [inv_inv, SemidirectProduct.inv_right, hgen, inverse_action] using hc
    rwa [he] at h
  have hA : A = ⊤ := by
    obtain ⟨v,hv,hv0⟩ : ∃ v : SixPointTernaryQuarterTurnNormalGenerators.Vector, v ∈ A ∧ v ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hAne
      apply le_antisymm ?_ bot_le
      intro v hv
      exact (Submodule.mem_bot (R := ZMod 3)).mpr (hn v hv)
    apply top_unique
    intro w _
    obtain ⟨k,hk⟩ := TernaryPlaneDihedralAffineNormalGenerators.combination_spans v hv0 w
    rw [← hk]
    exact A.add_mem (A.toAddSubgroup.nsmul_mem hv _)
      (A.toAddSubgroup.nsmul_mem (hJ v hv) _)
  apply top_unique
  intro g _
  let h := lift ^ g.right.toAdd.val
  have hh : h ∈ K := K.pow_mem hlift _
  have hhR : h.right = g.right := by
    change (rightHom : SixPointTernaryQuarterTurnNormalGenerators.Model →*
      SixPointTernaryQuarterTurnNormalGenerators.Upper) (lift ^ g.right.toAdd.val) = g.right
    rw [map_pow]
    change lift.right ^ g.right.toAdd.val = g.right
    rw [hgen, generator_pow]
  have hdR : (g*h⁻¹).right = 1 := by
    rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hhR, mul_inv_cancel]
  have hd : g*h⁻¹ ∈ K := by
    have hm : (g*h⁻¹).left.toAdd ∈ A := by rw [hA]; trivial
    change inl (g*h⁻¹).left ∈ K at hm
    have he : (inl (g*h⁻¹).left : SixPointTernaryQuarterTurnNormalGenerators.Model) = g*h⁻¹ := by
      apply SemidirectProduct.ext
      · rfl
      · exact hdR.symm
    rwa [he] at hm
  simpa only [inv_mul_cancel_right] using K.mul_mem hd hh

private theorem upper_binary : IsPGroup 2 SixPointTernaryQuarterTurnNormalGenerators.Upper := by
  apply IsPGroup.of_card (n := 2)
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  norm_num

theorem full_pullback (P : Subgroup (Equiv.Perm (Fin 6)))
    [MulAction.IsPretransitive P (Fin 6)]
    (hle : P ≤ SixPointTernaryQuarterTurnNormalGenerators.literalAction.range)
    (lift : SixPointTernaryQuarterTurnNormalGenerators.Model) (hlift : SixPointTernaryQuarterTurnNormalGenerators.literalAction lift ∈ P) (hgen : lift.right = SixPointTernaryQuarterTurnNormalGenerators.gen) :
    P.comap SixPointTernaryQuarterTurnNormalGenerators.literalAction = ⊤ := by
  let K := P.comap SixPointTernaryQuarterTurnNormalGenerators.literalAction
  let pi : K →* P := (SixPointTernaryQuarterTurnNormalGenerators.literalAction.comp K.subtype).codRestrict P (fun g => g.2)
  have hpi : Function.Surjective pi := by
    intro p
    obtain ⟨g,hg⟩ := hle p.2
    exact ⟨⟨g,by change SixPointTernaryQuarterTurnNormalGenerators.literalAction g ∈ P; rw [hg]; exact p.2⟩,Subtype.ext hg⟩
  let f : K →* SixPointTernaryQuarterTurnNormalGenerators.Upper := (rightHom : SixPointTernaryQuarterTurnNormalGenerators.Model →* SixPointTernaryQuarterTurnNormalGenerators.Upper).comp K.subtype
  have hn : f.ker ≠ ⊥ := by
    intro hb
    have hb2 : IsPGroup 2 K := upper_binary.of_injective f ((f.ker_eq_bot_iff).mp hb)
    exact PrimitiveSixFinalPublishedNormalGenerators.not_isPGroup P (hb2.of_surjective pi hpi)
  obtain ⟨g,hg,hg1⟩ := f.ker.bot_or_exists_ne_one.resolve_left hn
  apply full_of_nonzero_kernel K lift hlift hgen
  refine ⟨g,g.2,hg,?_⟩
  intro he
  exact hg1 (Subtype.ext he)

def inverseUpper : SixPointTernaryQuarterTurnNormalGenerators.Upper ≃* SixPointTernaryQuarterTurnNormalGenerators.Upper where
  toFun u := u⁻¹
  invFun u := u⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' a b := by simp [mul_comm]

private theorem linear_compatibility : ∀ (u : SixPointTernaryQuarterTurnNormalGenerators.Upper) (v : SixPointTernaryQuarterTurnNormalGenerators.Vector),
    SixPointTernaryQuarterTurnNormalGenerators.linearAction u v = TernaryPlaneDihedralAffineNormalGenerators.rotationHom u⁻¹ v := by decide +kernel

def affineEquiv : SixPointTernaryQuarterTurnNormalGenerators.Model ≃* AffineModel.Aff TernaryPlaneDihedralAffineNormalGenerators.rotationHom.range :=
  SemidirectProduct.congr (MulEquiv.refl _) (inverseUpper.trans
    (MonoidHom.ofInjective TernaryPlaneDihedralAffineNormalGenerators.rotationHom_injective)) (by
      intro u
      apply MulEquiv.ext
      intro v
      exact congrArg Multiplicative.ofAdd (linear_compatibility u v.toAdd))

def source {U : Non2UnipotentPrefixFiniteMenu.PreE7NonPairActionClass 6}
    (P : Subgroup (Equiv.Perm (Fin 6))) [MulAction.IsPretransitive P (Fin 6)]
    (E : Non2UnipotentPrefixFiniteMenu.preE7NonPairAction 6 U ≃* P)
    (hle : P ≤ SixPointTernaryQuarterTurnNormalGenerators.literalAction.range)
    (lift : SixPointTernaryQuarterTurnNormalGenerators.Model) (hlift : SixPointTernaryQuarterTurnNormalGenerators.literalAction lift ∈ P) (hgen : lift.right = SixPointTernaryQuarterTurnNormalGenerators.gen) :
    Non2UnipotentPrefixFiniteMenu.PreE7DegreeSixThreeSquaredC4Source U := by
  have hK := full_pullback P hle lift hlift hgen
  have heq : P = SixPointTernaryQuarterTurnNormalGenerators.literalAction.range := by
    apply le_antisymm hle
    rintro x ⟨g,rfl⟩
    have hg : g ∈ P.comap SixPointTernaryQuarterTurnNormalGenerators.literalAction := by rw [hK]; trivial
    exact hg
  exact {
    R := TernaryPlaneDihedralAffineNormalGenerators.rotationHom.range
    irreducible := TernaryPlaneDihedralAffineNormalGenerators.irreducible_of_quarterTurn _ ⟨Multiplicative.ofAdd 1,TernaryPlaneDihedralAffineNormalGenerators.rotationHom_one⟩
    topEquiv := (MonoidHom.ofInjective TernaryPlaneDihedralAffineNormalGenerators.rotationHom_injective).symm
    equiv := E.trans ((MulEquiv.subgroupCongr heq).trans
      ((MonoidHom.ofInjective action_injective).symm.trans affineEquiv)) }

end SymmetricSubgroupAsymptotics.DegreeSixThreeByTwoQuarterRecognition
