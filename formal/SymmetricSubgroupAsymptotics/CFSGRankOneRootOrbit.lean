import Mathlib.GroupTheory.GroupAction.Quotient

/-! The original root subgroup is regular on the non-base cosets.
Surjectivity uses the inverse of the original B*w*U cell; injectivity
uses the original opposite-root intersection, not group orders. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGRankOneRootOrbit
variable {G : Type*} [Group G] (B U : Subgroup G) (w : G)

theorem exists_root_transport
    (hcover : ∀ g : G, g∈B ∨ ∃ (b : B) (u : U),g=b.val*w*u.val)
    {x : G ⧸ B} (hx : x≠((1 : G) : G ⧸ B)) :
    ∃ u : U, (u : G) • ((w⁻¹ : G) : G ⧸ B)=x := by
  induction x using Quotient.inductionOn' with
  | h x =>
    have hn : x∉B := by
      intro hm
      apply hx
      apply QuotientGroup.eq.mpr
      simpa only [mul_one] using B.inv_mem hm
    have hi : x⁻¹∉B := fun h => hn (by simpa only [inv_inv] using B.inv_mem h)
    obtain ⟨b,u,he⟩ := (hcover x⁻¹).resolve_left hi
    have he' : x=(u : G)⁻¹*w⁻¹*(b : G)⁻¹ := by
      have hh := congrArg (fun g : G => g⁻¹) he
      simpa only [inv_inv,mul_inv_rev,mul_assoc] using hh
    refine ⟨u⁻¹,?_⟩
    change (((u : G)⁻¹*w⁻¹ : G) : G ⧸ B)=(x : G ⧸ B)
    apply QuotientGroup.eq.mpr
    rw [he']
    simpa [mul_assoc] using B.inv_mem b.property

theorem root_transport_injective
    (hcap : B ⊓ U.map (MulAut.conj w).toMonoidHom=⊥) :
    Function.Injective (fun u : U => (u : G) • ((w⁻¹ : G) : G ⧸ B)) := by
  intro u v he
  change (((u : G)*w⁻¹ : G) : G ⧸ B)=(((v : G)*w⁻¹ : G) : G ⧸ B) at he
  have hh := QuotientGroup.eq.mp he
  have hm : w*((u : G)⁻¹*(v : G))*w⁻¹∈B ⊓ U.map (MulAut.conj w).toMonoidHom := by
    refine ⟨?_,⟨(u : G)⁻¹*(v : G),U.mul_mem (U.inv_mem u.property) v.property,rfl⟩⟩
    simpa [mul_assoc] using hh
  rw [hcap] at hm
  change w*((u : G)⁻¹*(v : G))*w⁻¹=1 at hm
  have huv : (u : G)⁻¹*(v : G)=1 := by
    have hh := congrArg (fun g : G => w⁻¹*g*w) hm
    simpa [mul_assoc] using hh
  exact Subtype.ext (inv_mul_eq_one.mp huv)

end SymmetricSubgroupAsymptotics.CFSGRankOneRootOrbit
