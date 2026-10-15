import SymmetricSubgroupAsymptotics.TernaryFourAugmentationRepresentation
import SymmetricSubgroupAsymptotics.TernaryMonomialSemidirect

/-! The faithful augmentation affine group on the original twelve points.
The block labels use the centered four-triple chart. Every range statement
is about this actual permutation homomorphism. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TernaryFourAugmentationAffineImage

open TernaryFourAugmentationRepresentation SemidirectProduct

abbrev Points := Fin 4 × ZMod 3

def pointEquiv : Fin 12 ≃ Points where
  toFun x := ( #[(3,1),(2,2),(1,0),(0,1),(3,2),(2,0),
    (1,1),(0,2),(3,0),(2,1),(1,2),(0,0)] : Array Points)[x.val]!
  invFun p := (#[11,3,7,2,6,10,5,9,1,8,0,4] : Array (Fin 12))[3*p.1.val+p.2.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hom_injective : Function.Injective hom := by
  intro g h hgh
  have hlabel : Function.Injective
      (fun i : Fin 4 => fun j : Fin 3 => encode (Pi.single j 1) i) := by
    decide +kernel
  have hinv : g.symm = h.symm := by
    apply Equiv.ext
    intro i
    apply hlabel
    funext j
    have ht := congrArg (fun f : LinearGroup => encode (f (Pi.single j 1))) hgh
    change encode (hom g (Pi.single j 1)) = encode (hom h (Pi.single j 1)) at ht
    rw [encode_hom,encode_hom] at ht
    exact congrFun ht i
  exact congrArg Equiv.symm hinv

def blockEquiv : Equiv.Perm (Fin 4) ≃* hom.range := MonoidHom.ofInjective hom_injective

def blockMap (R : Subgroup LinearGroup) (hR : R ≤ hom.range) :
    R →* Equiv.Perm (Fin 4) :=
  blockEquiv.symm.toMonoidHom.comp (Subgroup.inclusion hR)

theorem hom_blockMap (R : Subgroup LinearGroup) (hR : R ≤ hom.range) (r : R) :
    hom (blockMap R hR r) = r.1 :=
  MonoidHom.apply_ofInjective_symm hom_injective ⟨r.1,hR r.2⟩

def fullMap (R : Subgroup LinearGroup) (hR : R ≤ hom.range) :
    AffineModel.Aff R →* TernaryMonomialSemidirect.Model
      (MonoidHom.id (Equiv.Perm (Fin 4))) (1 : Equiv.Perm (Fin 4) →* (ZMod 3)ˣ) :=
  SemidirectProduct.map encodeLinear.toAddMonoidHom.toMultiplicative
    (blockMap R hR) (by
      intro r
      apply MonoidHom.ext
      intro v
      apply Multiplicative.toAdd.injective
      change encode (r.1 v.toAdd) =
        fun i => (1 : ZMod 3) * encode v.toAdd ((blockMap R hR r)⁻¹ i)
      rw [← hom_blockMap R hR r,encode_hom]
      funext i
      exact (one_mul _).symm)

def translationPerm : Multiplicative Vector →* Equiv.Perm (Fin 12) :=
  pointEquiv.symm.permCongrHom.toMonoidHom.comp
    ((TernaryMonomialSemidirect.translations (X := Fin 4)).comp
      encodeLinear.toAddMonoidHom.toMultiplicative)

def blockPerm : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 12) :=
  pointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryMonomialSemidirect.complement
      (MonoidHom.id (Equiv.Perm (Fin 4))) (1 : Equiv.Perm (Fin 4) →* (ZMod 3)ˣ))

def action (R : Subgroup LinearGroup) (hR : R ≤ hom.range) :
    AffineModel.Aff R →* Equiv.Perm (Fin 12) :=
  pointEquiv.symm.permCongrHom.toMonoidHom.comp
    ((TernaryMonomialSemidirect.action
      (MonoidHom.id (Equiv.Perm (Fin 4))) (1 : Equiv.Perm (Fin 4) →* (ZMod 3)ˣ)).comp
        (fullMap R hR))

theorem action_inl (R : Subgroup LinearGroup) (hR : R ≤ hom.range)
    (v : Multiplicative Vector) : action R hR (inl v) = translationPerm v := by
  simp only [action,fullMap,MonoidHom.comp_apply,SemidirectProduct.map_inl,
    TernaryMonomialSemidirect.action,SemidirectProduct.lift_inl,translationPerm]

theorem action_inr (R : Subgroup LinearGroup) (hR : R ≤ hom.range) (r : R) :
    action R hR (inr r) = blockPerm (blockMap R hR r) := by
  simp only [action,fullMap,MonoidHom.comp_apply,SemidirectProduct.map_inr,
    TernaryMonomialSemidirect.action,SemidirectProduct.lift_inr,blockPerm]

theorem blockMap_hom (R : Subgroup LinearGroup) (hR : R ≤ hom.range)
    (g : Equiv.Perm (Fin 4)) (hg : hom g ∈ R) :
    blockMap R hR ⟨hom g,hg⟩ = g :=
  hom_injective (hom_blockMap R hR ⟨hom g,hg⟩)

/-- An actual nonzero translation and an irreducible pure linear image
recover every translation inside the same original permutation subgroup. -/
theorem translation_mem_of_irreducible
    (R : Subgroup LinearGroup) (hR : R ≤ hom.range)
    (hirr : AffineModel.Irreducible R) (H : Subgroup (Equiv.Perm (Fin 12)))
    (hlinear : ∀ r : R, blockPerm (blockMap R hR r) ∈ H)
    (v₀ : Vector) (hv₀ : v₀ ≠ 0)
    (ht : translationPerm (Multiplicative.ofAdd v₀) ∈ H)
    (v : Multiplicative Vector) : translationPerm v ∈ H := by
  let S : AddSubgroup Vector := {
    carrier := {w | translationPerm (Multiplicative.ofAdd w) ∈ H}
    zero_mem' := by
      change translationPerm (Multiplicative.ofAdd (0 : Vector)) ∈ H
      rw [ofAdd_zero,map_one]
      exact H.one_mem
    add_mem' := by
      intro x y hx hy
      change translationPerm (Multiplicative.ofAdd (x+y)) ∈ H
      rw [ofAdd_add,map_mul]
      exact H.mul_mem hx hy
    neg_mem' := by
      intro x hx
      change translationPerm (Multiplicative.ofAdd (-x)) ∈ H
      rw [ofAdd_neg,map_inv]
      exact H.inv_mem hx }
  have hstable : ∀ r ∈ R, ∀ w ∈ S, r w ∈ S := by
    intro r hr w hw
    let q : R := ⟨r,hr⟩
    have hconj : blockPerm (blockMap R hR q) *
        translationPerm (Multiplicative.ofAdd w) * (blockPerm (blockMap R hR q))⁻¹ =
        translationPerm (Multiplicative.ofAdd (r w)) := by
      simpa only [map_mul,map_inv,action_inl,action_inr,
        SemidirectProduct.right_inr,AffineModel.linAut_apply] using
        congrArg (action R hR)
          (AffineModel.conj_inl R (inr q) (Multiplicative.ofAdd w))
    change translationPerm (Multiplicative.ofAdd (r w)) ∈ H
    rw [← hconj]
    exact H.mul_mem (H.mul_mem (hlinear q) hw) (H.inv_mem (hlinear q))
  rcases hirr S hstable with hb | ht'
  · have hv : v₀ ∈ S := ht
    rw [hb] at hv
    exact (hv₀ (AddSubgroup.mem_bot.mp hv)).elim
  · have hv : v.toAdd ∈ S := by rw [ht']; exact AddSubgroup.mem_top _
    exact hv

theorem action_range_le (R : Subgroup LinearGroup) (hR : R ≤ hom.range)
    (H : Subgroup (Equiv.Perm (Fin 12)))
    (ht : ∀ v, translationPerm v ∈ H)
    (hl : ∀ r : R, blockPerm (blockMap R hR r) ∈ H) : (action R hR).range ≤ H := by
  rintro _ ⟨g,rfl⟩
  rw [← inl_left_mul_inr_right g,map_mul,action_inl,action_inr]
  exact H.mul_mem (ht g.left) (hl g.right)

end SymmetricSubgroupAsymptotics.TernaryFourAugmentationAffineImage

end
