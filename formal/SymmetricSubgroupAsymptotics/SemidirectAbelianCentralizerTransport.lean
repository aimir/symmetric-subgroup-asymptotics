import SymmetricSubgroupAsymptotics.SemidirectAbelianCentralizer

/-! Transport the translation kernel and its centralizer bound to the
literal group, keeping the actual kernel rather than an abstract substitute. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace SemidirectAbelianCentralizer

open SemidirectProduct

variable {G V H : Type*} [Group G] [CommGroup V] [Group H]
variable {φ : H →* MulAut V} (e : G ≃* V ⋊[φ] H)

def originalProjection : G →* H := rightHom.comp e.toMonoidHom

theorem originalProjection_surjective : Function.Surjective (originalProjection e) :=
  rightHom_surjective.comp e.surjective

def originalTranslation : V →* (originalProjection e).ker where
  toFun v := ⟨e.symm (inl v), by simp [originalProjection, MonoidHom.mem_ker]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' v w := by apply Subtype.ext; simp

theorem originalTranslation_bijective : Function.Bijective (originalTranslation e) := by
  constructor
  · intro v w hvw
    apply (inl_injective (φ := φ))
    exact e.symm.injective (congrArg Subtype.val hvw)
  · intro g
    refine ⟨(e g).left, ?_⟩
    apply Subtype.ext
    apply e.injective
    change e (e.symm (inl (e g).left)) = e g
    rw [e.apply_symm_apply]
    apply SemidirectProduct.ext
    · rfl
    · exact g.property.symm

noncomputable def originalTranslationEquiv : V ≃* (originalProjection e).ker :=
  MulEquiv.ofBijective (originalTranslation e) (originalTranslation_bijective e)

theorem originalTranslation_commutative : IsMulCommutative (originalProjection e).ker :=
  ⟨⟨fun a b => by
    apply (originalTranslationEquiv e).symm.injective
    simp only [map_mul, mul_comm]⟩⟩

theorem originalTranslation_card : Nat.card (originalProjection e).ker = Nat.card V :=
  (Nat.card_congr (originalTranslationEquiv e).toEquiv).symm

theorem originalTranslation_exponent (n : ℕ) (hn : ∀ v : V, v ^ n = 1)
    (g : (originalProjection e).ker) : g ^ n = 1 := by
  obtain ⟨v, rfl⟩ := (originalTranslationEquiv e).surjective g
  rw [← map_pow, hn, map_one]

theorem original_centralizer_map_projection :
    (Subgroup.centralizer ((originalProjection e).ker : Set G)).map
      (originalProjection e) = φ.ker := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    apply (mem_centralizer_iff φ (e g)).mp
    rw [Subgroup.mem_centralizer_iff]
    rintro x ⟨v, rfl⟩
    have hc := (Subgroup.mem_centralizer_iff.mp hg)
      (originalTranslation e v) (originalTranslation e v).property
    have he := congrArg e hc
    simp only [map_mul] at he
    change e (e.symm (inl v)) * e g = e g * e (e.symm (inl v)) at he
    simpa only [MulEquiv.apply_symm_apply] using he
  · intro hh
    refine ⟨e.symm (inr h), ?_, by simp [originalProjection]⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro g hg
    obtain ⟨v, hv⟩ := originalTranslation_bijective e |>.2 ⟨g, hg⟩
    have hge : g = e.symm (inl v) := (congrArg Subtype.val hv).symm
    rw [hge]
    have hc := (Subgroup.mem_centralizer_iff.mp
      ((mem_centralizer_iff φ (inr h)).mpr hh)) (inl v) ⟨v, rfl⟩
    simpa only [map_mul] using congrArg e.symm hc

theorem original_centralizer_quotient_card :
    Nat.card ((Subgroup.centralizer ((originalProjection e).ker : Set G)).map
      (QuotientGroup.mk' (originalProjection e).ker)) = Nat.card φ.ker := by
  let C := Subgroup.centralizer ((originalProjection e).ker : Set G)
  let q := QuotientGroup.mk' (originalProjection e).ker
  let f := QuotientGroup.quotientKerEquivOfSurjective (originalProjection e)
    (originalProjection_surjective e)
  have hcomp : f.toMonoidHom.comp q = originalProjection e := by ext g; rfl
  have hmap : (C.map q).map f.toMonoidHom = φ.ker := by
    rw [Subgroup.map_map, hcomp]
    exact original_centralizer_map_projection e
  calc
    Nat.card (C.map q) = Nat.card ((C.map q).map f.toMonoidHom) :=
      Nat.card_congr (f.subgroupMap (C.map q)).toEquiv
    _ = Nat.card φ.ker := by rw [hmap]

end SemidirectAbelianCentralizer
end SymmetricSubgroupAsymptotics

end
