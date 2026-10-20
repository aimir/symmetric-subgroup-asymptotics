import SymmetricSubgroupAsymptotics.BinaryPlaneDualOrbit

/-! The binary-plane local orbit coefficient through an actual quotient,
with the chart prime kept as an explicit binder. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k A B V : Type} [Field k] [Group A] [Group B]
    [AddCommGroup V] [Module k V]

theorem dualNonzeroOrbitCard_comp_surjective (rho : Representation k B V)
    (f : A →* B) (hf : Function.Surjective f) :
    Nat.card (Quotient (representationNonzeroOrbitRel (Representation.dual (rho.comp f))))=
      Nat.card (Quotient (representationNonzeroOrbitRel rho.dual)) := by
  apply Nat.card_congr
  apply Quotient.congr (Equiv.refl _)
  intro x y
  change (∃ a : A,(Representation.dual (rho.comp f)) a x.val=y.val) ↔ ∃ b : B,rho.dual b x.val=y.val
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨f a,?_⟩
    simpa only [Representation.dual_apply,MonoidHom.comp_apply,map_inv] using ha
  · rintro ⟨b,hb⟩
    obtain ⟨a,rfl⟩ := hf b
    refine ⟨a,?_⟩
    simpa only [Representation.dual_apply,MonoidHom.comp_apply,map_inv] using hb

theorem prime_binaryPlane_dualOrbitCard_eq_one
    {p : ℕ} [Fact p.Prime] {C L W : Type} [Group C] [Finite C] [Group L]
    [AddCommGroup W] [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
    (hp : p=2) (sigma : Representation (ZMod p) C W) (rho : Representation (ZMod p) L W)
    (f : L →* C) (hf : Function.Surjective f) (hC : Nat.card C=3)
    (hdim : Module.finrank (ZMod p) W=2) (hsigma : Function.Injective sigma)
    (hfactor : rho=sigma.comp f) :
    Nat.card (Quotient (representationNonzeroOrbitRel rho.dual))=1 := by
  subst p
  rw [hfactor]
  exact (dualNonzeroOrbitCard_comp_surjective sigma f hf).trans
    (binaryPlane_dual_nonzero_orbit_card_one sigma hC hdim hsigma)

end SymmetricSubgroupAsymptotics
