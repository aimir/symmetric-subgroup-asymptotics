import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupKernelChart
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-! Uniform module bounds and coprime module bounds on arbitrary affine
subgroups. All bounds pass through the actual projection image and the
actual retained translation submodule, then through any supplied original
surjective quotient map. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupSocles

open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart

variable {p : ℕ} [Fact p.Prime]
  {R V : Type} [Group R] [Finite R] [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V]
  (rho : R →* (V ≃ₗ[ZMod p] V)) (K : Subgroup (Model rho))

theorem quotient_normalGen (a : ℕ)
    (himage : ∀ L : Subgroup (Image rho K), L.Normal → MarkedC4.normalGen L ≤ a)
    (L : Subgroup (K ⧸ kernel rho K)) [L.Normal] : MarkedC4.normalGen L ≤ a :=
  CoprimeKernelQuotientSocles.normalGen_image_bound
    (quotientEquiv rho K).symm.toMonoidHom (quotientEquiv rho K).symm.surjective
    a himage L

theorem normalGen_le (t a : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound (imageRepresentation rho K) t)
    (himage : ∀ L : Subgroup (Image rho K), L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup K) [N.Normal] : MarkedC4.normalGen N ≤ t+a := by
  apply ElementaryUniformNormalGenerators.normalGen_le
    (kernel rho K) (chart rho K) t a (uniform rho K t huniform) ?_ N
  intro L hL
  letI := hL
  exact quotient_normalGen rho K a himage L

theorem quotientSocle (t a : ℕ)
    (huniform : UniformSubrepresentationGeneratorBound (imageRepresentation rho K) t)
    (himage : ∀ L : Subgroup (Image rho K), L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup K) [N.Normal] : SocleNormalGeneratorBound (K ⧸ N) (t+a) := by
  apply quotientSocleNormalGeneratorBound_of_normal_generating_tuples ?_ N
  intro L hL
  letI := hL
  exact exists_normal_generating_tuple_of_normalGen_le L
    (normalGen_le rho K t a huniform himage L)

theorem coprime_socle_of_surjective
    (hcop : Nat.Coprime p (Nat.card (Image rho K))) (t a : ℕ)
    (hgen : RepresentationGeneratedBy (imageRepresentation rho K) t)
    (himage : ∀ L : Subgroup (Image rho K), L.Normal → MarkedC4.normalGen L ≤ a)
    {Q : Type} [Group Q] (pi : K →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q (max t a) := by
  letI : NeZero (Nat.card (Image rho K) : ZMod p) := ⟨by
    intro hzero
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop)
      ((ZMod.natCast_eq_zero_iff _ _).mp hzero)⟩
  have huniform : UniformSubrepresentationGeneratorBound (imageRepresentation rho K) t :=
    RepresentationGeneratedBy.uniform_of_invertible_order (imageRepresentation rho K) hgen
  have hcopQuotient : Nat.Coprime p (Nat.card (K ⧸ kernel rho K)) := by
    rw [Nat.card_congr (quotientEquiv rho K).toEquiv]
    exact hcop
  apply CoprimeKernelQuotientSocles.socle_of_surjective p (kernel rho K)
    (CoprimeCyclicElementarySocles.kernel_isPGroup (kernel rho K) (chart rho K))
    hcopQuotient t a ?_ ?_ pi hpi
  · intro L hL hLE
    letI := hL
    exact ElementaryUniformNormalGenerators.kernel_normalGen_le
      (kernel rho K) (chart rho K) t (uniform rho K t huniform) L hLE
  · intro L hL
    letI := hL
    exact quotient_normalGen rho K a himage L

theorem coprime_quotientSocle
    (hcop : Nat.Coprime p (Nat.card (Image rho K))) (t a : ℕ)
    (hgen : RepresentationGeneratedBy (imageRepresentation rho K) t)
    (himage : ∀ L : Subgroup (Image rho K), L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup K) [N.Normal] : SocleNormalGeneratorBound (K ⧸ N) (max t a) :=
  coprime_socle_of_surjective rho K hcop t a hgen himage
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupSocles

end
