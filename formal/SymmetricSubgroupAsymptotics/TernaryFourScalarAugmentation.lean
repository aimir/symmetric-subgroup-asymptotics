import SymmetricSubgroupAsymptotics.TernaryFourAugmentationAffineImage
import SymmetricSubgroupAsymptotics.AffineIrreducibleQuotientSocles
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Scalar augmentation actions retain both the actual block homomorphism
and the actual scalar character. Joint faithfulness of these two maps is
proved to imply faithfulness on the ternary augmentation module. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryFourScalarAugmentation

open TernaryFourAugmentationRepresentation SemidirectProduct

variable {R : Type} [Group R]
variable (b : R →* Equiv.Perm (Fin 4)) (s : R →* (ZMod 3)ˣ)

def linearHom : R →* LinearGroup where
  toFun g := (hom (b g)).trans (LinearEquiv.smulOfUnit (s g))
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change (s 1 : ZMod 3) • hom (b 1) v = v
    rw [map_one,map_one,map_one]
    exact one_smul (ZMod 3) v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change (s (g*h) : ZMod 3) • hom (b (g*h)) v =
      (s g : ZMod 3) • hom (b g) ((s h : ZMod 3) • hom (b h) v)
    rw [s.map_mul,b.map_mul,hom.map_mul,LinearEquiv.mul_apply,map_smul,smul_smul]
    rfl

theorem encode_linearHom (g : R) (v : Vector) :
    encode (linearHom b s g v) =
      fun i => (s g : ZMod 3) * encode v ((b g).symm i) := by
  change encodeLinear ((s g : ZMod 3) • hom (b g) v) = _
  rw [map_smul]
  change (s g : ZMod 3) • encode (hom (b g) v) = _
  rw [encode_hom]
  rfl

theorem linearHom_injective
    (hsep : Function.Injective (fun g : R => (s g,b g))) :
    Function.Injective (linearHom b s) := by
  intro g h hgh
  have hlabels : Function.Injective (fun z : (ZMod 3)ˣ × Fin 4 =>
      fun j : Fin 3 => (z.1 : ZMod 3) * encode (Pi.single j 1) z.2) := by
    decide +kernel
  have hp (i : Fin 4) : (s g,(b g).symm i) = (s h,(b h).symm i) := by
    apply hlabels
    funext j
    have ht := congrArg (fun f : LinearGroup => encode (f (Pi.single j 1))) hgh
    change encode (linearHom b s g (Pi.single j 1)) =
      encode (linearHom b s h (Pi.single j 1)) at ht
    rw [encode_linearHom,encode_linearHom] at ht
    exact congrFun ht i
  have hs : s g = s h :=
    congrArg (fun z : (ZMod 3)ˣ × Fin 4 => z.1) (hp 0)
  have hi : (b g).symm = (b h).symm := by
    apply Equiv.ext
    intro i
    exact congrArg (fun z : (ZMod 3)ˣ × Fin 4 => z.2) (hp i)
  exact hsep (Prod.ext hs (congrArg Equiv.symm hi))

abbrev linearGroup := (linearHom b s).range

theorem irreducible_of_even_lifts
    (heven : ∀ g : alternatingGroup (Fin 4), ∃ r : R, b r = g.1 ∧ s r = 1) :
    AffineModel.Irreducible (linearGroup b s) := by
  apply irreducible_of_even_range_le
  rintro _ ⟨g,rfl⟩
  obtain ⟨r,hb,hs⟩ := heven g
  refine ⟨r,?_⟩
  apply LinearEquiv.ext
  intro v
  change (s r : ZMod 3) • hom (b r) v = hom g.1 v
  rw [hb,hs]
  exact one_smul (ZMod 3) _

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model (linearHom b s)

def complementEquiv (hsep : Function.Injective (fun g : R => (s g,b g))) :
    R ≃* linearGroup b s :=
  MonoidHom.ofInjective (linearHom_injective b s hsep)

def affineEquiv (hsep : Function.Injective (fun g : R => (s g,b g))) :
    Model b s ≃* AffineModel.Aff (linearGroup b s) :=
  SemidirectProduct.congr (MulEquiv.refl (Multiplicative Vector))
    (complementEquiv b s hsep) (by
      intro g
      apply MulEquiv.ext
      intro v
      rfl)

theorem socle_of_surjective
    (hsep : Function.Injective (fun g : R => (s g,b g)))
    (hirr : AffineModel.Irreducible (linearGroup b s))
    (v : Vector) (hv : v ≠ 0) {t : ℕ} (ht : 1 ≤ t)
    (hR : ∀ N : Subgroup R, ∀ _ : N.Normal, SocleNormalGeneratorBound (R ⧸ N) t)
    {Q : Type} [Group Q] (pi : Model b s →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q t := by
  apply AffineModel.socle_of_surjective_of_irreducible_complement_quotients
    (linearGroup b s) hirr v hv ht _
    (pi.comp (affineEquiv b s hsep).symm.toMonoidHom)
    (hpi.comp (affineEquiv b s hsep).symm.surjective)
  intro N hN
  letI := hN
  let q := (QuotientGroup.mk' N).comp (complementEquiv b s hsep).toMonoidHom
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective N).comp (complementEquiv b s hsep).surjective
  exact CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective q hq) (hR q.ker inferInstance)

def fullMap : Model b s →* TernaryMonomialSemidirect.Model b s :=
  SemidirectProduct.map encodeLinear.toAddMonoidHom.toMultiplicative
    (MonoidHom.id R) (by
      intro g
      apply MonoidHom.ext
      intro v
      apply Multiplicative.toAdd.injective
      change encode (linearHom b s g v.toAdd) =
        fun i => (s g : ZMod 3) * encode v.toAdd (b g⁻¹ i)
      rw [b.map_inv]
      exact encode_linearHom b s g v.toAdd)

def blockPerm : R →* Equiv.Perm (Fin 12) :=
  TernaryFourAugmentationAffineImage.pointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryMonomialSemidirect.complement b s)

def action : Model b s →* Equiv.Perm (Fin 12) :=
  TernaryFourAugmentationAffineImage.pointEquiv.symm.permCongrHom.toMonoidHom.comp
    ((TernaryMonomialSemidirect.action b s).comp (fullMap b s))

theorem action_inl (v : Multiplicative Vector) :
    action b s (inl v) = TernaryFourAugmentationAffineImage.translationPerm v := by
  simp only [action,fullMap,MonoidHom.comp_apply,SemidirectProduct.map_inl,
    TernaryMonomialSemidirect.action,SemidirectProduct.lift_inl,
    TernaryFourAugmentationAffineImage.translationPerm]

theorem action_inr (g : R) : action b s (inr g) = blockPerm b s g := by
  simp only [action,fullMap,MonoidHom.comp_apply,SemidirectProduct.map_inr,
    TernaryMonomialSemidirect.action,SemidirectProduct.lift_inr,blockPerm,MonoidHom.id_apply]

theorem translation_mem_of_irreducible
    (hirr : AffineModel.Irreducible (linearGroup b s))
    (H : Subgroup (Equiv.Perm (Fin 12))) (hblocks : ∀ g, blockPerm b s g ∈ H)
    (v₀ : Vector) (hv₀ : v₀ ≠ 0)
    (ht : TernaryFourAugmentationAffineImage.translationPerm (Multiplicative.ofAdd v₀) ∈ H)
    (v : Multiplicative Vector) : TernaryFourAugmentationAffineImage.translationPerm v ∈ H := by
  let t := TernaryFourAugmentationAffineImage.translationPerm
  let S : AddSubgroup Vector := {
    carrier := {w | t (Multiplicative.ofAdd w) ∈ H}
    zero_mem' := by
      change t (Multiplicative.ofAdd (0 : Vector)) ∈ H
      rw [ofAdd_zero,map_one]
      exact H.one_mem
    add_mem' := by
      intro x y hx hy
      change t (Multiplicative.ofAdd (x+y)) ∈ H
      rw [ofAdd_add,map_mul]
      exact H.mul_mem hx hy
    neg_mem' := by
      intro x hx
      change t (Multiplicative.ofAdd (-x)) ∈ H
      rw [ofAdd_neg,map_inv]
      exact H.inv_mem hx }
  have hstable : ∀ r ∈ linearGroup b s, ∀ w ∈ S, r w ∈ S := by
    rintro r ⟨g,rfl⟩ w hw
    have he : blockPerm b s g * t (Multiplicative.ofAdd w) * (blockPerm b s g)⁻¹ =
        t (Multiplicative.ofAdd (linearHom b s g w)) := by
      simpa only [map_mul,map_inv,action_inl,action_inr,SemidirectProduct.right_inr] using
        congrArg (action b s) (LinearSemidirectCoprimeSocleBounds.conjugate_translation
          (linearHom b s) (inr g) (Multiplicative.ofAdd w))
    change t (Multiplicative.ofAdd (linearHom b s g w)) ∈ H
    rw [← he]
    exact H.mul_mem (H.mul_mem (hblocks g) hw) (H.inv_mem (hblocks g))
  rcases hirr S hstable with hb | ht'
  · have hv : v₀ ∈ S := ht
    rw [hb] at hv
    exact (hv₀ (AddSubgroup.mem_bot.mp hv)).elim
  · have hv : v.toAdd ∈ S := by rw [ht']; exact AddSubgroup.mem_top _
    exact hv

end SymmetricSubgroupAsymptotics.TernaryFourScalarAugmentation

end
