import SymmetricSubgroupAsymptotics.TernaryFourAugmentationAffineImage

/-! The sign-twisted augmentation action of literal S4. On A4 the action
is unchanged, so the existing actual augmentation irreducibility proof
applies. The original S4 complement and original twelve-point map are
retained throughout. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryFourSignedAugmentation

open TernaryFourAugmentationRepresentation SemidirectProduct

def scalar : Equiv.Perm (Fin 4) →* (ZMod 3)ˣ :=
  (Units.map (Int.castRingHom (ZMod 3)).toMonoidHom).comp Equiv.Perm.sign

def twistedHom : Equiv.Perm (Fin 4) →* LinearGroup where
  toFun g := (hom g).trans (LinearEquiv.smulOfUnit (scalar g))
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change (scalar 1 : ZMod 3) • hom 1 v = v
    rw [map_one,map_one]
    exact one_smul (ZMod 3) v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change (scalar (g*h) : ZMod 3) • hom (g*h) v =
      (scalar g : ZMod 3) • hom g ((scalar h : ZMod 3) • hom h v)
    rw [scalar.map_mul,hom.map_mul,LinearEquiv.mul_apply,map_smul,smul_smul]
    rfl

theorem scalar_even (g : Equiv.Perm (Fin 4)) (hg : g ∈ alternatingGroup (Fin 4)) :
    scalar g = 1 := by
  change Units.map (Int.castRingHom (ZMod 3)).toMonoidHom (Equiv.Perm.sign g) = 1
  rw [Equiv.Perm.mem_alternatingGroup.mp hg,map_one]

theorem twistedHom_even (g : Equiv.Perm (Fin 4)) (hg : g ∈ alternatingGroup (Fin 4)) :
    twistedHom g = hom g := by
  apply LinearEquiv.ext
  intro v
  change (scalar g : ZMod 3) • hom g v = hom g v
  rw [scalar_even g hg]
  exact one_smul (ZMod 3) _

theorem encode_twistedHom (g : Equiv.Perm (Fin 4)) (v : Vector) :
    encode (twistedHom g v) =
      fun i => (scalar g : ZMod 3) * encode v (g.symm i) := by
  change encodeLinear ((scalar g : ZMod 3) • hom g v) = _
  rw [map_smul]
  change (scalar g : ZMod 3) • encode (hom g v) = _
  rw [encode_hom]
  rfl

theorem twistedHom_injective : Function.Injective twistedHom := by
  intro g h hgh
  have hlabels : Function.Injective (fun z : (ZMod 3)ˣ × Fin 4 =>
      fun j : Fin 3 => (z.1 : ZMod 3) * encode (Pi.single j 1) z.2) := by
    decide +kernel
  have hinv : g.symm = h.symm := by
    apply Equiv.ext
    intro i
    have hp : (scalar g,g.symm i) = (scalar h,h.symm i) := by
      apply hlabels
      funext j
      have ht := congrArg (fun f : LinearGroup => encode (f (Pi.single j 1))) hgh
      change encode (twistedHom g (Pi.single j 1)) =
        encode (twistedHom h (Pi.single j 1)) at ht
      rw [encode_twistedHom,encode_twistedHom] at ht
      exact congrFun ht i
    exact congrArg Prod.snd hp
  exact congrArg Equiv.symm hinv

abbrev linearGroup := twistedHom.range

theorem irreducible : AffineModel.Irreducible linearGroup :=
  irreducible_of_even_range_le _ (by
    rintro _ ⟨g,rfl⟩
    exact ⟨g.1,twistedHom_even g.1 g.2⟩)

theorem linear_normal_total (A B : Subgroup linearGroup)
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective twistedHom.rangeRestrict
    twistedHom.rangeRestrict_surjective NaturalFourNormalChains.symmetric_normal_total A B hA hB

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model twistedHom

def complementEquiv : Equiv.Perm (Fin 4) ≃* linearGroup :=
  MonoidHom.ofInjective twistedHom_injective

def affineEquiv : Model ≃* AffineModel.Aff linearGroup :=
  SemidirectProduct.congr (MulEquiv.refl (Multiplicative Vector)) complementEquiv (by
    intro g
    apply MulEquiv.ext
    intro v
    rfl)

theorem normal_total : ∀ A B : Subgroup Model,
    A.Normal → B.Normal → A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective affineEquiv.symm.toMonoidHom affineEquiv.symm.surjective
    (AffineModel.normal_total_of_irreducible_complement _ irreducible linear_normal_total)

theorem socle_of_surjective {Q : Type} [Group Q]
    (pi : Model →* Q) (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 1 :=
  socleNormalGeneratorBound_one_of_normal_total
    (normalSubgroups_total_of_surjective pi hpi normal_total)

def fullMap : Model →* TernaryMonomialSemidirect.Model
    (MonoidHom.id (Equiv.Perm (Fin 4))) scalar :=
  SemidirectProduct.map encodeLinear.toAddMonoidHom.toMultiplicative
    (MonoidHom.id (Equiv.Perm (Fin 4))) (by
      intro g
      apply MonoidHom.ext
      intro v
      apply Multiplicative.toAdd.injective
      exact encode_twistedHom g v.toAdd)

def blockPerm : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 12) :=
  TernaryFourAugmentationAffineImage.pointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryMonomialSemidirect.complement (MonoidHom.id (Equiv.Perm (Fin 4))) scalar)

def action : Model →* Equiv.Perm (Fin 12) :=
  TernaryFourAugmentationAffineImage.pointEquiv.symm.permCongrHom.toMonoidHom.comp
    ((TernaryMonomialSemidirect.action (MonoidHom.id (Equiv.Perm (Fin 4))) scalar).comp fullMap)

theorem action_inl (v : Multiplicative Vector) :
    action (inl v) = TernaryFourAugmentationAffineImage.translationPerm v := by
  simp only [action,fullMap,MonoidHom.comp_apply,SemidirectProduct.map_inl,
    TernaryMonomialSemidirect.action,SemidirectProduct.lift_inl,
    TernaryFourAugmentationAffineImage.translationPerm]

theorem action_inr (g : Equiv.Perm (Fin 4)) : action (inr g) = blockPerm g := by
  simp only [action,fullMap,MonoidHom.comp_apply,SemidirectProduct.map_inr,
    TernaryMonomialSemidirect.action,SemidirectProduct.lift_inr,blockPerm,MonoidHom.id_apply]

theorem translation_mem_of_irreducible (H : Subgroup (Equiv.Perm (Fin 12)))
    (hblocks : ∀ g, blockPerm g ∈ H) (v₀ : Vector) (hv₀ : v₀ ≠ 0)
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
  have hstable : ∀ r ∈ linearGroup, ∀ w ∈ S, r w ∈ S := by
    rintro r ⟨g,rfl⟩ w hw
    have he : blockPerm g * t (Multiplicative.ofAdd w) * (blockPerm g)⁻¹ =
        t (Multiplicative.ofAdd (twistedHom g w)) := by
      simpa only [map_mul,map_inv,action_inl,action_inr,SemidirectProduct.right_inr] using
        congrArg action (LinearSemidirectCoprimeSocleBounds.conjugate_translation
          twistedHom (inr g) (Multiplicative.ofAdd w))
    change t (Multiplicative.ofAdd (twistedHom g w)) ∈ H
    rw [← he]
    exact H.mul_mem (H.mul_mem (hblocks g) hw) (H.inv_mem (hblocks g))
  rcases irreducible S hstable with hb | ht'
  · have hv : v₀ ∈ S := ht
    rw [hb] at hv
    exact (hv₀ (AddSubgroup.mem_bot.mp hv)).elim
  · have hv : v.toAdd ∈ S := by rw [ht']; exact AddSubgroup.mem_top _
    exact hv

end SymmetricSubgroupAsymptotics.TernaryFourSignedAugmentation

end
