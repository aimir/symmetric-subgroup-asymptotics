import SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopModuleEnvelope

/-! Internal scalar transport and exhaustive actual-normal-denominator
case split for the top coordinate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopScalarEnvelope
open BinaryFourBlockAugmentation BinaryFourSymmetricBlockActions

abbrev Envelope (p : ℕ) := (Fin 3 → ZMod p) × ((Fin 2 → ZMod p) × (Fin 2 → ZMod p))

def representation {R : Type} [Group R] {p : ℕ} (hp : p = 2)
    (beta : R →* SymmetricComplement) : Representation (ZMod p) R (Envelope p) := by
  subst p
  exact symmetricEnvelopeRepresentation.comp beta

def Support {p : ℕ} (x : Envelope p) : Prop := x.1 0 = 0 ∧ x.1 1 = 0 ∧ x.2.1 = 0

variable {R V : Type} [Group R] [AddCommGroup V] {p : ℕ} [Fact p.Prime] [Module (ZMod p) V]

theorem s4_top_intertwiner [FiniteDimensional (ZMod p) V]
    (hp : p = 2) (N : Subgroup SymmetricComplement) [N.Normal]
    (beta : R →* SymmetricComplement) (rho : Representation (ZMod p) R V)
    (f : Multiplicative V →* SymmetricComplement ⧸ N) (hf : Function.Injective f)
    (hH : f.range.Normal) (hbinary : IsPGroup 2 f.range)
    (hconj : ∀ r v, f (Multiplicative.ofAdd (rho r v)) =
      QuotientGroup.mk' N (beta r) * f (Multiplicative.ofAdd v) *
        (QuotientGroup.mk' N (beta r))⁻¹) :
    ∃ i : rho.IntertwiningMap (representation hp beta),
      Function.Injective i ∧ ∀ v, Support (i v) := by
  subst p
  by_cases hN : N = ⊥
  · subst N
    let e := QuotientGroup.quotientBot (G := SymmetricComplement)
    let f0 := e.toMonoidHom.comp f
    have hf0 : Function.Injective f0 := e.injective.comp hf
    have hn0 : f0.range.Normal := by
      dsimp only [f0]
      rw [MonoidHom.range_comp]
      exact Subgroup.Normal.map hH _ e.surjective
    have hb0 : IsPGroup 2 f0.range := by
      dsimp only [f0]
      rw [MonoidHom.range_comp]
      exact hbinary.map _
    have hc0 : ∀ r v, f0 (Multiplicative.ofAdd (rho r v)) =
        beta r * f0 (Multiplicative.ofAdd v) * (beta r)⁻¹ := by
      intro r v
      have h := congrArg e (hconj r v)
      simpa only [f0,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_mul,map_inv] using h
    exact BinaryFourCanonicalTopModuleEnvelope.unquotiented_top_intertwiner
      beta rho f0 hf0 hn0 hb0 hc0
  · exact BinaryFourCanonicalTopModuleEnvelope.nonzero_top_intertwiner
      N hN beta rho f hf hH hbinary hconj

theorem a4_top_intertwiner
    (hp : p = 2) (N : Subgroup Complement) [N.Normal]
    (beta : R →* Complement) (rho : Representation (ZMod p) R V)
    (f : Multiplicative V →* Complement ⧸ N) (hf : Function.Injective f)
    (hH : f.range.Normal) (hbinary : IsPGroup 2 f.range)
    (hconj : ∀ r v, f (Multiplicative.ofAdd (rho r v)) =
      QuotientGroup.mk' N (beta r) * f (Multiplicative.ofAdd v) *
        (QuotientGroup.mk' N (beta r))⁻¹) :
    ∃ i : rho.IntertwiningMap (representation hp (SemidirectProduct.inl.comp beta)),
      Function.Injective i ∧ (∀ v, Support (i v)) ∧ (∀ v, (i v).1 2 = 0) := by
  subst p
  by_cases hN : N = ⊥
  · subst N
    let e := QuotientGroup.quotientBot (G := Complement)
    let f0 := e.toMonoidHom.comp f
    have hf0 : Function.Injective f0 := e.injective.comp hf
    have hn0 : f0.range.Normal := by
      dsimp only [f0]
      rw [MonoidHom.range_comp]
      exact Subgroup.Normal.map hH _ e.surjective
    have hb0 : IsPGroup 2 f0.range := by
      dsimp only [f0]
      rw [MonoidHom.range_comp]
      exact hbinary.map _
    have hc0 : ∀ r v, f0 (Multiplicative.ofAdd (rho r v)) =
        beta r * f0 (Multiplicative.ofAdd v) * (beta r)⁻¹ := by
      intro r v
      have h := congrArg e (hconj r v)
      simpa only [f0,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_mul,map_inv] using h
    exact BinaryFourCanonicalTopModuleEnvelope.a4_unquotiented_top_intertwiner
      beta rho f0 hf0 hn0 hb0 hc0
  · exact BinaryFourCanonicalTopModuleEnvelope.a4_nonzero_top_intertwiner
      N hN beta rho f hf hbinary

end SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopScalarEnvelope
end
