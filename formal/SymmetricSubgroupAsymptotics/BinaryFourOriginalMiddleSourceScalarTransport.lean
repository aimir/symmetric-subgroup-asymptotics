import SymmetricSubgroupAsymptotics.BinaryFourA4OriginalSocleAssembly
import SymmetricSubgroupAsymptotics.BinaryFourOriginalScalarCharts

/-! Internal transport of the complete middle-source and final assembly
interfaces to the original affine prime parameter. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourSymmetricBlockActions

variable {G W : Type} [Group G]

abbrev EnvelopeAt (p : ℕ) := (Fin 3 → ZMod p) × ((Fin 2 → ZMod p) × (Fin 2 → ZMod p))

def canonicalFullAt {p : ℕ} (hp : p = 2) (gamma : G →* SymmetricComplement) :
    Representation (ZMod p) G (Fin 8 → ZMod p) := by
  subst p
  exact canonicalFull.comp gamma

def canonicalEnvelopeAt {p : ℕ} (hp : p = 2) (gamma : G →* SymmetricComplement) :
    Representation (ZMod p) G (EnvelopeAt p) := by
  subst p
  exact symmetricEnvelopeRepresentation.comp gamma

def OriginalMiddleSourceAt {p : ℕ} [Fact p.Prime] (hp : p = 2)
    [AddCommGroup W] [_root_.Module (ZMod p) W]
    (gamma : G →* SymmetricComplement) (tau : Representation (ZMod p) G W) : Type 1 := by
  subst p
  exact OriginalMiddleSource gamma tau

theorem originalMiddleSource_exists_at {p : ℕ} [Fact p.Prime] (hp : p = 2)
    [AddCommGroup W] [_root_.Module (ZMod p) W]
    (gamma : G →* SymmetricComplement)
    (hgamma : ∀ r : Complement, ∃ g : G, gamma g = SemidirectProduct.inl r)
    (L : Subrepresentation (canonicalFullAt hp gamma))
    (tau : Representation (ZMod p) G W) (f : L.toRepresentation.IntertwiningMap tau)
    (hf : Function.Surjective f)
    (hfixed : ∀ g : G, gamma g ∈ BinaryFourSymmetricKleinNormalCover.klein →
      ∀ v : W, tau g v = v) : Nonempty (OriginalMiddleSourceAt hp gamma tau) := by
  subst p
  exact originalMiddleSource_exists gamma hgamma L tau f hf hfixed

local instance originalMiddleScalarTransport_representationModule
    {p : ℕ} [Fact p.Prime] [AddCommGroup W] [_root_.Module (ZMod p) W]
    (rho : Representation (ZMod p) G W) :
    _root_.Module (ZMod p)[G] rho.asModule :=
  Representation.instModuleMonoidAlgebraAsModule rho

theorem s4_original_socle_generated_at {p : ℕ} [Fact p.Prime] (hp : p = 2)
    [AddCommGroup W] [_root_.Module (ZMod p) W]
    (gamma : G →* SymmetricComplement) (hgamma : Function.Surjective gamma)
    (rho : Representation (ZMod p) G W)
    [IsSemisimpleModule (ZMod p)[G] rho.asModule]
    (T : Subrepresentation rho)
    (S : OriginalMiddleSourceAt hp gamma T.toRepresentation)
    (j : (rho.asModule ⧸ T.asSubmodule) →ₗ[(ZMod p)[G]] (canonicalEnvelopeAt hp gamma).asModule)
    (hj : Function.Injective j)
    (htop : ∀ x, let y := (canonicalEnvelopeAt hp gamma).asModuleEquiv (j x)
      y.1 0 = 0 ∧ y.1 1 = 0 ∧ y.2.1 = 0) : RepresentationGeneratedBy rho 2 := by
  subst p
  exact s4_original_socle_generated gamma hgamma rho T S j hj htop

theorem a4_original_socle_generated_at {p : ℕ} [Fact p.Prime] (hp : p = 2)
    [AddCommGroup W] [_root_.Module (ZMod p) W]
    (gamma : G →* Complement) (hgamma : Function.Surjective gamma)
    (rho : Representation (ZMod p) G W)
    [IsSemisimpleModule (ZMod p)[G] rho.asModule]
    (T : Subrepresentation rho)
    (S : OriginalMiddleSourceAt hp (SemidirectProduct.inl.comp gamma) T.toRepresentation)
    (j : (rho.asModule ⧸ T.asSubmodule) →ₗ[(ZMod p)[G]]
      (canonicalEnvelopeAt hp (SemidirectProduct.inl.comp gamma)).asModule)
    (hj : Function.Injective j)
    (htop : ∀ x, let y := (canonicalEnvelopeAt hp (SemidirectProduct.inl.comp gamma)).asModuleEquiv (j x)
      y.1 0 = 0 ∧ y.1 1 = 0 ∧ y.2.1 = 0)
    (hsix : ∀ x,
      ((canonicalEnvelopeAt hp (SemidirectProduct.inl.comp gamma)).asModuleEquiv (j x)).1 2 = 0) :
    RepresentationGeneratedBy rho 2 := by
  subst p
  exact a4_original_socle_generated gamma hgamma rho T S j hj htop hsix

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
