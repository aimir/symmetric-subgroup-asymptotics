import SymmetricSubgroupAsymptotics.ScalarPairSwapRepresentation
import SymmetricSubgroupAsymptotics.C2WreathTwistedDiagonal

/-! Exact images of paired scalar semidirect models in a local wreath.
The only local compatibility input is the displayed scalar conjugation
identity. Normal-generator bounds descend to the full actual image. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace ScalarPairSwapWreathImage

open SemidirectProduct

abbrev Binary := Multiplicative (ZMod 2)

variable (p : ℕ) [Fact p.Prime]
  {C A : Type} [Group C] [Group A]
  (alpha : Binary →* MulAut C) (chi : C →* (ZMod p)ˣ)
  (e : Multiplicative (ZMod p) →* A) (f : C →* A)

def translationCoordinates : Multiplicative (Fin 2 → ZMod p) →* A × A where
  toFun v := (e (Multiplicative.ofAdd (v.toAdd 0)), e (Multiplicative.ofAdd (v.toAdd 1)))
  map_one' := Prod.ext e.map_one e.map_one
  map_mul' _ _ := Prod.ext (e.map_mul _ _) (e.map_mul _ _)

def translations : Multiplicative (Fin 2 → ZMod p) →* C2Wreath.W A :=
  (inl : A × A →* C2Wreath.W A).comp (translationCoordinates p e)

def upper : ScalarPairSwapRepresentation.Upper alpha →* C2Wreath.W A :=
  C2WreathTwistedDiagonal.intoWreath alpha f

private theorem wreath_conj_inl (g : C2Wreath.W A) (v : A × A) :
    g * inl v * g⁻¹ = inl (g.left * C2Wreath.swapAut A g.right v * g.left⁻¹) := by
  conv_lhs => rw [← inl_left_mul_inr_right g]
  have h : (inr g.right : C2Wreath.W A) * inl v * (inr g.right)⁻¹ =
      inl (C2Wreath.swapAut A g.right v) := by
    rw [← map_inv]
    exact (inl_aut (φ := C2Wreath.swapAut A) g.right v).symm
  calc
    (inl g.left * inr g.right : C2Wreath.W A) * inl v * (inl g.left * inr g.right)⁻¹ =
        inl g.left * ((inr g.right : C2Wreath.W A) * inl v * (inr g.right)⁻¹) *
          (inl g.left)⁻¹ := by group
    _ = _ := by rw [h, ← map_inv, ← map_mul, ← map_mul]

private theorem scalarAction_apply (c : C) (b : Binary)
    (v : Multiplicative (Fin 2 → ZMod p)) :
    LinearSemidirectCoprimeSocleBounds.linearAction
        (ScalarPairSwapRepresentation.linearAction p alpha chi)
        (⟨c, b⟩ : ScalarPairSwapRepresentation.Upper alpha) v =
      Multiplicative.ofAdd ((ScalarPairSwapRepresentation.diagonal p alpha chi c)
        ((PrimePairWreathNormalGenerators.linearAction p b) v.toAdd)) := rfl

variable
  (hscalar : ∀ (c : C) (x : ZMod p),
    e (Multiplicative.ofAdd ((chi c : ZMod p) * x)) =
      f c * e (Multiplicative.ofAdd x) * (f c)⁻¹)

def intoWreath : ScalarPairSwapRepresentation.Model p alpha chi →* C2Wreath.W A :=
  SemidirectProduct.lift (translations p e) (upper alpha f) (by
    intro g
    apply MonoidHom.ext
    intro v
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases g with ⟨c, b⟩
    rw [scalarAction_apply]
    rcases C2Wreath.cases b with rfl | rfl
    · rw [map_one]
      change (inl
          (e (Multiplicative.ofAdd ((chi c : ZMod p) * v.toAdd 0)),
            e (Multiplicative.ofAdd ((chi (alpha C2Wreath.gen c) : ZMod p) * v.toAdd 1))) :
          C2Wreath.W A) =
        upper alpha f (⟨c, 1⟩ : ScalarPairSwapRepresentation.Upper alpha) *
          inl (e (Multiplicative.ofAdd (v.toAdd 0)), e (Multiplicative.ofAdd (v.toAdd 1))) *
            (upper alpha f (⟨c, 1⟩ : ScalarPairSwapRepresentation.Upper alpha))⁻¹
      rw [wreath_conj_inl]
      apply congrArg (inl : A × A → C2Wreath.W A)
      apply Prod.ext
      · change e (Multiplicative.ofAdd ((chi c : ZMod p) * v.toAdd 0)) =
          f c * e (Multiplicative.ofAdd (v.toAdd 0)) * (f c)⁻¹
        exact hscalar c (v.toAdd 0)
      · change e (Multiplicative.ofAdd ((chi (alpha C2Wreath.gen c) : ZMod p) * v.toAdd 1)) =
          f (alpha C2Wreath.gen c) * e (Multiplicative.ofAdd (v.toAdd 1)) *
            (f (alpha C2Wreath.gen c))⁻¹
        exact hscalar (alpha C2Wreath.gen c) (v.toAdd 1)
    · change (inl
          (e (Multiplicative.ofAdd ((chi c : ZMod p) * v.toAdd 1)),
            e (Multiplicative.ofAdd ((chi (alpha C2Wreath.gen c) : ZMod p) * v.toAdd 0))) :
          C2Wreath.W A) =
        upper alpha f (⟨c, C2Wreath.gen⟩ : ScalarPairSwapRepresentation.Upper alpha) *
          inl (e (Multiplicative.ofAdd (v.toAdd 0)), e (Multiplicative.ofAdd (v.toAdd 1))) *
            (upper alpha f (⟨c, C2Wreath.gen⟩ : ScalarPairSwapRepresentation.Upper alpha))⁻¹
      rw [wreath_conj_inl]
      apply congrArg (inl : A × A → C2Wreath.W A)
      apply Prod.ext
      · change e (Multiplicative.ofAdd ((chi c : ZMod p) * v.toAdd 1)) =
          f c * e (Multiplicative.ofAdd (v.toAdd 1)) * (f c)⁻¹
        exact hscalar c (v.toAdd 1)
      · change e (Multiplicative.ofAdd ((chi (alpha C2Wreath.gen c) : ZMod p) * v.toAdd 0)) =
          f (alpha C2Wreath.gen c) * e (Multiplicative.ofAdd (v.toAdd 0)) *
            (f (alpha C2Wreath.gen c))⁻¹
        exact hscalar (alpha C2Wreath.gen c) (v.toAdd 0))

def image : Subgroup (C2Wreath.W A) := (intoWreath p alpha chi e f hscalar).range

theorem normal_generating_tuples [Finite C] {a : ℕ}
    (hupper : ∀ N : Subgroup (ScalarPairSwapRepresentation.Upper alpha), N.Normal →
      ∃ x : Fin a → ScalarPairSwapRepresentation.Upper alpha,
        Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup (image p alpha chi e f hscalar), N.Normal →
      ∃ x : Fin (1 + a) → image p alpha chi e f hscalar,
        Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective (intoWreath p alpha chi e f hscalar).rangeRestrict
    (intoWreath p alpha chi e f hscalar).rangeRestrict_surjective
    (ScalarPairSwapRepresentation.normal_generating_tuples p alpha chi hupper)

end ScalarPairSwapWreathImage
end SymmetricSubgroupAsymptotics

end
