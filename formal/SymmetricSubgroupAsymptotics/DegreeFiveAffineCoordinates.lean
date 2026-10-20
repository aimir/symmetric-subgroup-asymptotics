import SymmetricSubgroupAsymptotics.DegreeFiveAffineClassification

/-!
# Literal coordinates for a regular normal subgroup on five points

Every faithful action on five points with a regular normal subgroup of
order five embeds into the natural affine group on `F₅`. The construction
uses the literal translation subgroup, its actual stabilizer, and their
already proved internal semidirect product.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeFiveAffineCoordinates

abbrev Translation := Multiplicative (AffineModel.V 5 1)

theorem translation_card : Nat.card Translation = 5 := by
  exact (Nat.card_congr Multiplicative.toAdd).trans F20.card_V

/-- In one dimension every automorphism of the additive translation group
is induced by a unique member of the natural linear complement. -/
def fullLinearEquiv : F20.R ≃* MulAut Translation := by
  apply MulEquiv.ofBijective (AffineModel.linAut F20.R)
  have hinj : Function.Injective (AffineModel.linAut F20.R) := by
    intro a b hab
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact congrArg Multiplicative.toAdd
      (DFunLike.congr_fun hab (Multiplicative.ofAdd v))
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨hinj, ?_⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : IsCyclic Translation := isCyclic_of_prime_card translation_card
  rw [Subgroup.card_top, F20.card_GLV, IsCyclic.card_mulAut, translation_card,
    Nat.totient_prime (by norm_num : Nat.Prime 5)]

@[simp] theorem fullLinearEquiv_apply (r : F20.R) :
    fullLinearEquiv r = AffineModel.linAut F20.R r := rfl

variable {L : Type} [Group L] [Finite L] [MulAction L (Fin 5)]
  [FaithfulSMul L (Fin 5)] (P : PrimitiveAffineProfile L (Fin 5))
  (x : Fin 5)

/-- The translation chart is an actual multiplicative isomorphism; its
choice changes only the labels of the five points. -/
def translationEquiv : P.V ≃* Translation := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact mulEquivOfPrimeCardEq (P.degreeFive_translation_card x) translation_card

/-- The faithful point stabilizer in linear coordinates. -/
def complementMap : P.complement x →* F20.R :=
  fullLinearEquiv.symm.toMonoidHom.comp
    ((MulAut.congr (translationEquiv P x)).toMonoidHom.comp (P.complementAction x))

theorem complementMap_injective : Function.Injective (complementMap P x) :=
  fullLinearEquiv.symm.injective.comp
    ((MulAut.congr (translationEquiv P x)).injective.comp
      (P.complementAction_injective x))

omit [FaithfulSMul L (Fin 5)] in
/-- The transported conjugation action is exactly the natural linear
action on the new translation coordinates. -/
theorem complementMap_compatible (c : P.complement x) (v : P.V) :
    translationEquiv P x (P.complementAction x c v) =
      AffineModel.linAut F20.R (complementMap P x c) (translationEquiv P x v) := by
  have h : AffineModel.linAut F20.R (complementMap P x c) =
      MulAut.congr (translationEquiv P x) (P.complementAction x c) := by
    exact fullLinearEquiv.apply_symm_apply _
  rw [h]
  simp

/-- Map the internal translation/stabilizer product to the natural affine
group. -/
def semidirectMap : P.V ⋊[P.complementAction x] P.complement x →* F20.G :=
  SemidirectProduct.map (translationEquiv P x).toMonoidHom (complementMap P x)
    (by
      intro c
      exact MonoidHom.ext (complementMap_compatible P x c))

theorem semidirectMap_injective : Function.Injective (semidirectMap P x) := by
  intro a b hab
  apply SemidirectProduct.ext
  · exact (translationEquiv P x).injective
      (congrArg SemidirectProduct.left hab)
  · exact complementMap_injective P x
      (congrArg SemidirectProduct.right hab)

/-- The original group embeds into the natural affine group, through its
proved internal semidirect-product isomorphism. -/
def embedding : L →* F20.G :=
  (semidirectMap P x).comp (P.semidirectEquiv x).symm.toMonoidHom

theorem embedding_injective : Function.Injective (embedding P x) :=
  (semidirectMap_injective P x).comp (P.semidirectEquiv x).symm.injective

/-- The labels of the original five points in the affine translation chart. -/
def pointEquiv : AffineModel.V 5 1 ≃ Fin 5 :=
  Multiplicative.ofAdd.trans
    ((translationEquiv P x).symm.toEquiv.trans (P.pointEquiv x))

omit [FaithfulSMul L (Fin 5)] in
theorem pointEquiv_translation (v : P.V) :
    pointEquiv P x (Multiplicative.toAdd (translationEquiv P x v)) =
      P.pointEquiv x v := by
  simp [pointEquiv]

omit [Finite L] [FaithfulSMul L (Fin 5)] in
/-- Stabilizer conjugation is the actual action in the translation chart. -/
theorem complement_point (c : P.complement x) (v : P.V) :
    P.pointEquiv x (P.complementAction x c v) = (c : L) • P.pointEquiv x v := by
  change ((c : L) * (v : L) * (c : L)⁻¹) • x = (c : L) • ((v : L) • x)
  rw [mul_smul, mul_smul]
  have hfix : (c : L)⁻¹ • x = x := (c⁻¹).property
  rw [hfix]

omit [Finite L] [FaithfulSMul L (Fin 5)] in
/-- The internal semidirect product acts by multiplication of translations
followed by its literal stabilizer conjugation action. -/
theorem semidirect_point
    (g : P.V ⋊[P.complementAction x] P.complement x) (v : P.V) :
    P.pointEquiv x (g.left * P.complementAction x g.right v) =
      P.semidirectEquiv x g • P.pointEquiv x v := by
  change ((g.left : L) *
    ((g.right : L) * (v : L) * (g.right : L)⁻¹)) • x =
      P.semidirectEquiv x g • P.pointEquiv x v
  have hval : P.semidirectEquiv x g = (g.left : L) * (g.right : L) := rfl
  rw [hval]
  change _ = ((g.left : L) * (g.right : L)) • ((v : L) • x)
  rw [mul_smul, mul_smul, mul_smul, mul_smul]
  have hfix : (g.right : L)⁻¹ • x = x := (g.right⁻¹).property
  rw [hfix]

omit [FaithfulSMul L (Fin 5)] in
/-- The embedding preserves the actual permutation actions after the
displayed relabelling of points. -/
theorem embedding_point (g : L) (v : AffineModel.V 5 1) :
    pointEquiv P x (AffineModel.action F20.R (embedding P x g) v) =
      g • pointEquiv P x v := by
  obtain ⟨a, rfl⟩ := (P.semidirectEquiv x).surjective g
  obtain ⟨w, rfl⟩ := (translationEquiv P x).surjective (Multiplicative.ofAdd v)
  rw [show embedding P x (P.semidirectEquiv x a) = semidirectMap P x a by
    change semidirectMap P x ((P.semidirectEquiv x).symm (P.semidirectEquiv x a)) = _
    rw [MulEquiv.symm_apply_apply]]
  have hcoord : AffineModel.action F20.R (semidirectMap P x a)
      (Multiplicative.toAdd (translationEquiv P x w)) =
      Multiplicative.toAdd (translationEquiv P x
        (a.left * P.complementAction x a.right w)) := by
    change Multiplicative.toAdd (translationEquiv P x a.left) +
      (complementMap P x a.right : AffineModel.GLV 5 1)
        (Multiplicative.toAdd (translationEquiv P x w)) = _
    rw [map_mul]
    have h := congrArg Multiplicative.toAdd (complementMap_compatible P x a.right w)
    exact congrArg (fun z => Multiplicative.toAdd (translationEquiv P x a.left) + z)
      h.symm
  change pointEquiv P x (AffineModel.action F20.R (semidirectMap P x a)
      (Multiplicative.toAdd (translationEquiv P x w))) =
    P.semidirectEquiv x a • pointEquiv P x
      (Multiplicative.toAdd (translationEquiv P x w))
  rw [hcoord, pointEquiv_translation, pointEquiv_translation]
  exact semidirect_point P x a w

end DegreeFiveAffineCoordinates
end SymmetricSubgroupAsymptotics

end
