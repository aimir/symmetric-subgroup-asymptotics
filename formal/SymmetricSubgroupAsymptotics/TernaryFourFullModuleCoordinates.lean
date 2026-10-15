import SymmetricSubgroupAsymptotics.TernaryFourAugmentationCentralCore
import SymmetricSubgroupAsymptotics.TernaryA4SectionRegularEmbedding

/-! The full original four-coordinate module is the direct sum of its
augmentation and its fixed diagonal, because four is one in F3. The
resulting group map is from the actual augmentation affine group times C3.
The invariant lattice is reused literally, with no submodule enumeration. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.TernaryFourFullModuleCoordinates

open TernaryFourAugmentationRepresentation SemidirectProduct

abbrev FullVector := Fin 4 → ZMod 3
abbrev C3 := Multiplicative (ZMod 3)
abbrev FullModel := TernaryMonomialSemidirect.Model
  (MonoidHom.id (Equiv.Perm (Fin 4))) (1 : Equiv.Perm (Fin 4) →* (ZMod 3)ˣ)

def constant : ZMod 3 →ₗ[ZMod 3] FullVector where
  toFun c _ := c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def diagonal : C3 →* FullModel :=
  (inl : Multiplicative FullVector →* FullModel).comp constant.toAddMonoidHom.toMultiplicative

def pointAction : FullModel →* Equiv.Perm (Fin 12) :=
  TernaryFourAugmentationAffineImage.pointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryMonomialSemidirect.action
      (MonoidHom.id (Equiv.Perm (Fin 4))) (1 : Equiv.Perm (Fin 4) →* (ZMod 3)ˣ))

def translation : Multiplicative FullVector →* Equiv.Perm (Fin 12) :=
  pointAction.comp inl

def diagonalPerm : C3 →* Equiv.Perm (Fin 12) := pointAction.comp diagonal

theorem pointAction_inl (v : Multiplicative FullVector) :
    pointAction (inl v) = translation v := rfl

theorem pointAction_inr (g : Equiv.Perm (Fin 4)) :
    pointAction (inr g) = TernaryFourAugmentationAffineImage.blockPerm g := by
  simp only [pointAction,MonoidHom.comp_apply,TernaryMonomialSemidirect.action,
    SemidirectProduct.lift_inr,TernaryFourAugmentationAffineImage.blockPerm]

theorem augmentation_translation (v : Multiplicative Vector) :
    translation (Multiplicative.ofAdd (encode v.toAdd)) =
      TernaryFourAugmentationAffineImage.translationPerm v := by
  simp only [translation,pointAction,MonoidHom.comp_apply,TernaryMonomialSemidirect.action,
    SemidirectProduct.lift_inl,TernaryFourAugmentationAffineImage.translationPerm]
  apply congrArg TernaryFourAugmentationAffineImage.pointEquiv.symm.permCongrHom.toMonoidHom
  apply congrArg TernaryMonomialSemidirect.translations
  apply Multiplicative.toAdd.injective
  change encode v.toAdd = encodeLinear v.toAdd
  rfl

theorem diagonal_translation (z : C3) :
    diagonalPerm z = translation (Multiplicative.ofAdd (constant z.toAdd)) := rfl

theorem conjugate_translation (g : Equiv.Perm (Fin 4)) (v : FullVector) :
    TernaryFourAugmentationAffineImage.blockPerm g * translation (Multiplicative.ofAdd v) *
      (TernaryFourAugmentationAffineImage.blockPerm g)⁻¹ =
      translation (Multiplicative.ofAdd (TernaryA4InvariantSubmodules.coordinateAction g v)) := by
  have he := congrArg pointAction
    (LinearSemidirectCoprimeSocleBounds.conjugate_translation
      (TernaryMonomialSemidirect.linearAction
        (MonoidHom.id (Equiv.Perm (Fin 4))) (1 : Equiv.Perm (Fin 4) →* (ZMod 3)ˣ))
      (inr g) (Multiplicative.ofAdd v))
  have hlin : LinearSemidirectCoprimeSocleBounds.linearAction
      (TernaryMonomialSemidirect.linearAction
        (MonoidHom.id (Equiv.Perm (Fin 4))) (1 : Equiv.Perm (Fin 4) →* (ZMod 3)ˣ))
      g (Multiplicative.ofAdd v) =
        Multiplicative.ofAdd (TernaryA4InvariantSubmodules.coordinateAction g v) := by
    apply Multiplicative.toAdd.injective
    funext i
    change (1 : ZMod 3) * v (g.symm i) = v (g.symm i)
    exact one_mul _
  simpa only [map_mul,map_inv,pointAction_inl,pointAction_inr,
    SemidirectProduct.right_inr,hlin] using he

variable (R : Subgroup LinearGroup) (hR : R ≤ hom.range)

theorem diagonal_commutes (g : AffineModel.Aff R) (z : C3) :
    Commute (TernaryFourAugmentationAffineImage.fullMap R hR g) (diagonal z) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    change encode g.left.toAdd i + (1 : ZMod 3) * z.toAdd =
      z.toAdd + (1 : ZMod 3) * encode g.left.toAdd i
    simp only [one_mul,add_comm]
  · change TernaryFourAugmentationAffineImage.blockMap R hR g.right * 1 =
      1 * TernaryFourAugmentationAffineImage.blockMap R hR g.right
    simp

def fullMap : AffineModel.Aff R × C3 →* FullModel where
  toFun g := TernaryFourAugmentationAffineImage.fullMap R hR g.1 * diagonal g.2
  map_one' := by
    simp only [Prod.fst_one,Prod.snd_one,map_one,mul_one]
  map_mul' g h := by
    change TernaryFourAugmentationAffineImage.fullMap R hR (g.1*h.1) * diagonal (g.2*h.2) = _
    rw [map_mul,map_mul]
    calc
      _ = TernaryFourAugmentationAffineImage.fullMap R hR g.1 *
          (TernaryFourAugmentationAffineImage.fullMap R hR h.1 * diagonal g.2) * diagonal h.2 := by group
      _ = TernaryFourAugmentationAffineImage.fullMap R hR g.1 *
          (diagonal g.2 * TernaryFourAugmentationAffineImage.fullMap R hR h.1) * diagonal h.2 := by
        rw [(diagonal_commutes R hR h.1 g.2).eq]
      _ = _ := by group

def action : AffineModel.Aff R × C3 →* Equiv.Perm (Fin 12) :=
  pointAction.comp (fullMap R hR)

theorem action_apply (g : AffineModel.Aff R) (z : C3) :
    action R hR (g,z) = TernaryFourAugmentationAffineImage.action R hR g * diagonalPerm z :=
  pointAction.map_mul _ _

theorem action_translation (v : Vector) (z : ZMod 3) :
    action R hR (inl (Multiplicative.ofAdd v),Multiplicative.ofAdd z) =
      translation (Multiplicative.ofAdd (encode v + constant z)) := by
  rw [action_apply,TernaryFourAugmentationAffineImage.action_inl,
    diagonal_translation,← augmentation_translation,← map_mul,← ofAdd_add]
  rfl

theorem action_complement (r : R) :
    action R hR (inr r,1) =
      TernaryFourAugmentationAffineImage.blockPerm
        (TernaryFourAugmentationAffineImage.blockMap R hR r) := by
  rw [action_apply,TernaryFourAugmentationAffineImage.action_inr,map_one,mul_one]

/-- Exact original additive-subgroup classification, valid for every
normal translation intersection invariant under the even block action. -/
theorem invariant_lattice (K : AddSubgroup FullVector)
    (hK : ∀ g ∈ alternatingGroup (Fin 4), ∀ v ∈ K,
      TernaryA4InvariantSubmodules.coordinateAction g v ∈ K) :
    K = ⊥ ∨ K = TernaryA4InvariantSubmodules.diagonal.toAddSubgroup ∨
      K = TernaryA4InvariantSubmodules.augmentation.toAddSubgroup ∨ K = ⊤ :=
  TernaryA4InvariantSubmodules.additive_classification K hK

def unitSeed : FullVector := Pi.single 0 1

theorem full_translation_mem (H : Subgroup (Equiv.Perm (Fin 12)))
    (hblocks : ∀ g ∈ alternatingGroup (Fin 4),
      TernaryFourAugmentationAffineImage.blockPerm g ∈ H)
    (hseed : translation (Multiplicative.ofAdd unitSeed) ∈ H)
    (v : Multiplicative FullVector) : translation v ∈ H := by
  let S : AddSubgroup FullVector := {
    carrier := {w | translation (Multiplicative.ofAdd w) ∈ H}
    zero_mem' := by
      change translation (Multiplicative.ofAdd (0 : FullVector)) ∈ H
      rw [ofAdd_zero,map_one]
      exact H.one_mem
    add_mem' := by
      intro x y hx hy
      change translation (Multiplicative.ofAdd (x+y)) ∈ H
      rw [ofAdd_add,map_mul]
      exact H.mul_mem hx hy
    neg_mem' := by
      intro x hx
      change translation (Multiplicative.ofAdd (-x)) ∈ H
      rw [ofAdd_neg,map_inv]
      exact H.inv_mem hx }
  have hstable : ∀ g ∈ alternatingGroup (Fin 4), ∀ w ∈ S,
      TernaryA4InvariantSubmodules.coordinateAction g w ∈ S := by
    intro g hg w hw
    change translation (Multiplicative.ofAdd (TernaryA4InvariantSubmodules.coordinateAction g w)) ∈ H
    rw [← conjugate_translation]
    exact H.mul_mem (H.mul_mem (hblocks g hg) hw) (H.inv_mem (hblocks g hg))
  have hs : unitSeed ∈ S := hseed
  have htop : S = ⊤ := by
    rcases invariant_lattice S hstable with hb | hd | ha | ht
    · rw [hb,AddSubgroup.mem_bot] at hs
      have he := congrFun hs 0
      norm_num [unitSeed] at he
    · rw [hd] at hs
      have he := hs (1 : Fin 4)
      norm_num [unitSeed] at he
    · rw [ha] at hs
      change (∑ i : Fin 4, unitSeed i) = 0 at hs
      norm_num [unitSeed] at hs
    · exact ht
  have hv : v.toAdd ∈ S := by rw [htop]; exact AddSubgroup.mem_top _
  exact hv

/-- Explicit coordinate decomposition, retaining the original full vector. -/
theorem exists_augmentation_constant (v : FullVector) :
    ∃ u : Vector, ∃ z : ZMod 3, encode u + constant z = v := by
  let z : ZMod 3 := ∑ i, v i
  let w : FullVector := v - constant z
  have hw : ∑ i, w i = 0 := by
    have hwi (i : Fin 4) : w i = v i - z := by
      simp [w,constant]
    have hfour : ∀ a : ZMod 3, (4 : ℕ) • a = a := by decide +kernel
    simp_rw [hwi]
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
    change z - (4 : ℕ) • z = 0
    rw [hfour z,sub_self]
  refine ⟨decode w,z,?_⟩
  rw [encode_decode w hw]
  exact sub_add_cancel v (constant z)

end SymmetricSubgroupAsymptotics.TernaryFourFullModuleCoordinates

end
