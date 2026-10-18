import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailSource
import SymmetricSubgroupAsymptotics.IrreducibleCharacterLabels

/-! Exact transport of a Y1 certificate through an actual quotient-group
equivalence. Counts, slots, scalar layers and central weight are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace ScalarFourHeadedQuotient
variable {G H : Type} [Group G] [Group H]

def kernelEquiv (h : ScalarFourHeadedQuotient H) (e : G ≃* H) :
    (h.top.comp e.toMonoidHom).ker ≃* h.top.ker :=
  MulEquiv.ofBijective
    ((e.toMonoidHom.comp (h.top.comp e.toMonoidHom).ker.subtype).codRestrict h.top.ker
      (by intro p; exact p.2)) (by
        constructor
        · intro x y he
          exact Subtype.ext (e.injective (congrArg Subtype.val he))
        · intro p
          refine ⟨⟨e.symm p,?_⟩,?_⟩
          · change h.top (e (e.symm p))=1
            rw [e.apply_symm_apply]
            exact p.2
          · exact Subtype.ext (e.apply_symm_apply p))

def centerEquiv (h : ScalarFourHeadedQuotient H) (e : G ≃* H) :
    (h.center.comap (kernelEquiv h e).toMonoidHom) ≃* h.center :=
  MulEquiv.ofBijective
    ({
      toFun := fun z => ⟨kernelEquiv h e z,z.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) } :
      (h.center.comap (kernelEquiv h e).toMonoidHom) →* h.center) (by
        constructor
        · intro x y he
          exact Subtype.ext ((kernelEquiv h e).injective (congrArg Subtype.val he))
        · intro z
          refine ⟨⟨(kernelEquiv h e).symm z,?_⟩,?_⟩
          · change kernelEquiv h e ((kernelEquiv h e).symm z) ∈ h.center
            rw [MulEquiv.apply_symm_apply]
            exact z.2
          · exact Subtype.ext ((kernelEquiv h e).apply_symm_apply z))

def comapEquiv (h : ScalarFourHeadedQuotient H) (e : G ≃* H) :
    ScalarFourHeadedQuotient G where
  top := h.top.comp e.toMonoidHom
  top_surjective := h.top_surjective.comp e.surjective
  center := h.center.comap (kernelEquiv h e).toMonoidHom
  center_comm := by
    intro z hz p
    apply (kernelEquiv h e).injective
    simp only [map_mul]
    exact h.center_comm _ hz _
  center_twoGroup := h.center_twoGroup.of_equiv (centerEquiv h e).symm
  layers := h.layers
  coord j := (h.coord j).comp (kernelEquiv h e).toMonoidHom
  coord_center := fun j z hz => h.coord_center j _ hz
  coord_joint := fun p hp => h.coord_joint _ hp
  coord_twisted := by
    intro g p j
    change h.coord j (kernelEquiv h e (MulAut.conjNormal g p)) = _
    have he : kernelEquiv h e (MulAut.conjNormal g p) =
        MulAut.conjNormal (e g) (kernelEquiv h e p) := by
      apply Subtype.ext
      change e (g*(p : G)*g⁻¹)=e g*e (p : G)*(e g)⁻¹
      simp only [map_mul,map_inv]
    rw [he,h.coord_twisted]
    rfl
  coord_zero_surjective := h.coord_zero_surjective.comp (kernelEquiv h e).surjective

theorem comapEquiv_weight (h : ScalarFourHeadedQuotient H) (e : G ≃* H) :
    (h.comapEquiv e).weight=h.weight := by
  change (h.layers+1)+Nat.log 2 (Nat.card (h.center.comap (kernelEquiv h e).toMonoidHom)) = _
  rw [Nat.card_congr (centerEquiv h e).toEquiv]
  rfl
end ScalarFourHeadedQuotient

namespace CharacterQuotientCertificate
variable {G H : Type} [Group G] [Group H]
private def representationComap (rho : FiniteIrreducibleRepresentation ℂ H) (e : G ≃* H) :
    FiniteIrreducibleRepresentation ℂ G where
  Space := rho.Space
  addCommGroup := inferInstance
  module := inferInstance
  finiteDimensional := inferInstance
  action := rho.action.comp e.toMonoidHom
  irreducible := representation_irreducible_comp rho.action e.toMonoidHom e.surjective

def comapEquiv (c : CharacterQuotientCertificate H) (e : G ≃* H) :
    CharacterQuotientCertificate G where
  mode := c.mode
  tuple := {
    binaryCount := c.tuple.binaryCount
    linearCount := c.tuple.linearCount
    generalCount := c.tuple.generalCount
    binary i := (c.tuple.binary i).comp e.toMonoidHom
    binary_twoGroup := by
      intro i
      apply (c.tuple.binary_twoGroup i).to_le
      rintro _ ⟨x,rfl⟩
      exact ⟨e x,rfl⟩
    linear i := (c.tuple.linear i).comp e.toMonoidHom
    general i := representationComap (c.tuple.general i) e
    faithful := by
      intro g hb hl hg
      apply e.injective
      exact (c.tuple.faithful (e g) hb hl hg).trans e.map_one.symm }
  prime := c.prime
  known := fun hm => ⟨(c.known hm).1,(c.known hm).2.of_equiv e.symm⟩

theorem comapEquiv_slope (c : CharacterQuotientCertificate H) (e : G ≃* H) :
    (c.comapEquiv e).slope=c.slope := rfl
end CharacterQuotientCertificate

namespace Non2UnipotentPrefixFiniteMenu.PreE7Y1QuotientCertificate
variable {G H : Type} [Group G] [Group H]
def comapEquiv (C : PreE7Y1QuotientCertificate H) (e : G ≃* H) :
    PreE7Y1QuotientCertificate G :=
  match C with
  | .character c hc => .character (c.comapEquiv e)
      (by simpa only [CharacterQuotientCertificate.comapEquiv_slope] using hc)
  | .headed h hh => .headed (h.comapEquiv e)
      (by simpa only [ScalarFourHeadedQuotient.comapEquiv_weight] using hh)
end Non2UnipotentPrefixFiniteMenu.PreE7Y1QuotientCertificate
end SymmetricSubgroupAsymptotics
end
