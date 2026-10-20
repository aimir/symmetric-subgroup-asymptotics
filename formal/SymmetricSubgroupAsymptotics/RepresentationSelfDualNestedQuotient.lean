import SymmetricSubgroupAsymptotics.RepresentationGeneratorExtension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Duality for nested quotients in a self-dual representation

Let `A ≤ B ≤ V`, where `V` has an equivariant perfect pairing.  The dual of
`B / A` is the quotient `A^⊥ / B^⊥`.  This file records the statement at
the representation level, using the literal nested subrepresentations and
quotients.  It is the reusable bridge from finite orthogonal-state tables to
one-generator certificates for quotient duals.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

universe u

variable {k G V : Type u} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- Contragredient commutes equivariantly with pullback along a group map.
The underlying linear equivalence is the identity; the only calculation is
that a homomorphism preserves inverses. -/
def representationDualCompEquiv
    {H : Type u} [Group H] (rho : Representation k G V) (f : H →* G) :
    (Representation.dual (rho.comp f)).Equiv (rho.dual.comp f) :=
  Representation.Equiv.mk (LinearEquiv.refl k (Module.Dual k V)) (by
    intro h
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro v
    change phi (rho (f h⁻¹) v) = phi (rho (f h)⁻¹ v)
    rw [map_inv])

/-- Regard `A` as a subrepresentation of `B` when both sit in the same
ambient representation. -/
def nestedSubrepresentation
    {rho : Representation k G V} (A B : Subrepresentation rho)
    (hAB : A ≤ B) : Subrepresentation B.toRepresentation where
  toSubmodule := A.toSubmodule.comap B.toSubmodule.subtype
  apply_mem_toSubmodule g x hx := by
    change rho g x.1 ∈ A
    exact A.apply_mem_toSubmodule g hx

/-- Forgetting the outer subtype identifies the nested copy of `A` with
`A` itself. -/
def nestedSubrepresentationEquiv
    {rho : Representation k G V} (A B : Subrepresentation rho)
    (hAB : A ≤ B) :
    A.toSubmodule ≃ₗ[k] (nestedSubrepresentation A B hAB).toSubmodule where
  toFun := fun a => ⟨⟨a.1, hAB a.2⟩, a.2⟩
  invFun := fun a => ⟨a.1.1, a.2⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_nestedSubrepresentation
    [FiniteDimensional k V]
    {rho : Representation k G V} (A B : Subrepresentation rho)
    (hAB : A ≤ B) :
    Module.finrank k (nestedSubrepresentation A B hAB).toSubmodule =
      Module.finrank k A.toSubmodule :=
  (nestedSubrepresentationEquiv A B hAB).finrank_eq.symm

/-- The literal representation on `B / A`. -/
def nestedQuotientRepresentation
    {rho : Representation k G V} (A B : Subrepresentation rho)
    (hAB : A ≤ B) : Representation k G
      (B.toSubmodule ⧸ (nestedSubrepresentation A B hAB).toSubmodule) :=
  B.toRepresentation.quotient
    (nestedSubrepresentation A B hAB).toSubmodule (fun g x hx =>
      (nestedSubrepresentation A B hAB).apply_mem_toSubmodule g hx)

/-- Orthogonal complement of an invariant subrepresentation under a chosen
equivariant self-duality. -/
def selfDualOrthogonalSubrepresentation
    (rho : Representation k G V) (e : rho.Equiv rho.dual)
    (A : Subrepresentation rho) : Subrepresentation rho where
  toSubmodule := A.toSubmodule.dualAnnihilator.comap e.toLinearMap
  apply_mem_toSubmodule g x hx := by
    rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator] at hx ⊢
    intro a ha
    have he := Representation.IntertwiningMap.isIntertwining
      rho rho.dual e.toIntertwiningMap g x
    change e (rho g x) a = 0
    have hev := congrArg (fun ell : Module.Dual k V => ell a) he
    change e (rho g x) a = e x (rho g⁻¹ a) at hev
    exact hev.trans (hx _ (A.apply_mem_toSubmodule g⁻¹ ha))

/-- Orthogonal complementation reverses inclusion. -/
theorem selfDualOrthogonalSubrepresentation_antitone
    (rho : Representation k G V) (e : rho.Equiv rho.dual)
    {A B : Subrepresentation rho} (hAB : A ≤ B) :
    selfDualOrthogonalSubrepresentation rho e B ≤
      selfDualOrthogonalSubrepresentation rho e A := by
  intro x hx
  change e x ∈ B.toSubmodule.dualAnnihilator at hx
  change e x ∈ A.toSubmodule.dualAnnihilator
  rw [Submodule.mem_dualAnnihilator] at hx ⊢
  intro a ha
  exact hx a (hAB ha)

/-- Pair `A^⊥` with `B/A`.  Equivariance is exactly invariance of the
chosen self-dual pairing. -/
noncomputable def selfDualNestedPairing
    (rho : Representation k G V) (e : rho.Equiv rho.dual)
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    Representation.IntertwiningMap
      (selfDualOrthogonalSubrepresentation rho e A).toRepresentation
      (Representation.dual (nestedQuotientRepresentation A B hAB)) where
  toLinearMap :=
    { toFun := fun d =>
        (nestedSubrepresentation A B hAB).toSubmodule.liftQ
          { toFun := fun b => e d.1 b.1
            map_add' := by intro x y; exact map_add (e d.1) x.1 y.1
            map_smul' := by intro c x; exact map_smul (e d.1) c x.1 }
          (by
            intro b hb
            change e d.1 b.1 = 0
            have hd := d.property
            change e d.1 ∈ A.toSubmodule.dualAnnihilator at hd
            rw [Submodule.mem_dualAnnihilator] at hd
            exact hd b.1 hb)
      map_add' := by
        intro d f
        apply LinearMap.ext
        intro y
        obtain ⟨b, rfl⟩ :=
          (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective y
        change e (d.1 + f.1) b.1 = e d.1 b.1 + e f.1 b.1
        simp only [map_add, LinearMap.add_apply]
      map_smul' := by
        intro c d
        apply LinearMap.ext
        intro y
        obtain ⟨b, rfl⟩ :=
          (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective y
        change e (c • d.1) b.1 = c • e d.1 b.1
        simp only [map_smul, LinearMap.smul_apply] }
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro d
    apply LinearMap.ext
    intro y
    obtain ⟨b, rfl⟩ :=
      (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective y
    have heq := Representation.IntertwiningMap.isIntertwining
      rho rho.dual e.toIntertwiningMap g d.1
    change e (rho g d.1) b.1 = e d.1 (rho g⁻¹ b.1)
    have hev := congrArg (fun ell : Module.Dual k V => ell b.1) heq
    change e (rho g d.1) b.1 = e d.1 (rho g⁻¹ b.1) at hev
    exact hev

/-- Every functional on `B/A` extends to the ambient self-dual space, so
the pairing map from `A^⊥` is onto. -/
theorem selfDualNestedPairing_surjective
    [FiniteDimensional k V]
    (rho : Representation k G V) (e : rho.Equiv rho.dual)
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    Function.Surjective (selfDualNestedPairing rho e A B hAB) := by
  intro psi
  let psiB : Module.Dual k B.toSubmodule :=
    psi.comp (nestedSubrepresentation A B hAB).toSubmodule.mkQ
  obtain ⟨phi, hphi⟩ := (Subspace.dualRestrict_surjective (W := B.toSubmodule)) psiB
  obtain ⟨v, hv⟩ := e.surjective phi
  have hvOrth : v ∈ selfDualOrthogonalSubrepresentation rho e A := by
    change e v ∈ A.toSubmodule.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator]
    intro a ha
    let b : B.toSubmodule := ⟨a, hAB ha⟩
    have hr := LinearMap.congr_fun hphi b
    change phi a = psiB b at hr
    have hvEval := congrArg (fun ell : Module.Dual k V => ell a) hv
    change e v a = phi a at hvEval
    rw [hvEval, hr]
    change psi (Submodule.Quotient.mk b) = 0
    have hbzero : (Submodule.Quotient.mk b :
        B.toSubmodule ⧸ (nestedSubrepresentation A B hAB).toSubmodule) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact ha
    rw [hbzero, map_zero]
  let d : (selfDualOrthogonalSubrepresentation rho e A).toSubmodule :=
    ⟨v, hvOrth⟩
  refine ⟨d, ?_⟩
  apply LinearMap.ext
  intro y
  obtain ⟨b, rfl⟩ :=
    (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective y
  have hr := LinearMap.congr_fun hphi b
  change phi b.1 = psiB b at hr
  change e v b.1 = psi (Submodule.Quotient.mk b)
  have hvEval := congrArg (fun ell : Module.Dual k V => ell b.1) hv
  change e v b.1 = phi b.1 at hvEval
  exact hvEval.trans hr

/-- The kernel of the pairing on `A^⊥` is exactly `B^⊥`. -/
theorem selfDualNestedPairing_ker
    (rho : Representation k G V) (e : rho.Equiv rho.dual)
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    (selfDualNestedPairing rho e A B hAB).toLinearMap.ker =
      (nestedSubrepresentation
        (selfDualOrthogonalSubrepresentation rho e B)
        (selfDualOrthogonalSubrepresentation rho e A)
        (selfDualOrthogonalSubrepresentation_antitone rho e hAB)).toSubmodule := by
  ext d
  constructor
  · intro hd
    change selfDualNestedPairing rho e A B hAB d = 0 at hd
    change d.1 ∈ selfDualOrthogonalSubrepresentation rho e B
    change e d.1 ∈ B.toSubmodule.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator]
    intro b hb
    let bB : B.toSubmodule := ⟨b, hb⟩
    have hz := LinearMap.congr_fun hd
      (Submodule.Quotient.mk bB)
    change e d.1 b = 0 at hz
    exact hz
  · intro hd
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro y
    obtain ⟨b, rfl⟩ :=
      (nestedSubrepresentation A B hAB).toSubmodule.mkQ_surjective y
    change e d.1 b.1 = 0
    change e d.1 ∈ B.toSubmodule.dualAnnihilator at hd
    rw [Submodule.mem_dualAnnihilator] at hd
    exact hd b.1 b.2

/-- Quotient the pairing by its exact kernel. -/
noncomputable def selfDualNestedQuotientIntertwiner
    (rho : Representation k G V) (e : rho.Equiv rho.dual)
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    (nestedQuotientRepresentation
      (selfDualOrthogonalSubrepresentation rho e B)
      (selfDualOrthogonalSubrepresentation rho e A)
      (selfDualOrthogonalSubrepresentation_antitone rho e hAB)).IntertwiningMap
        (Representation.dual (nestedQuotientRepresentation A B hAB)) where
  toLinearMap :=
    (nestedSubrepresentation
      (selfDualOrthogonalSubrepresentation rho e B)
      (selfDualOrthogonalSubrepresentation rho e A)
      (selfDualOrthogonalSubrepresentation_antitone rho e hAB)).toSubmodule.liftQ
        (selfDualNestedPairing rho e A B hAB).toLinearMap (by
          intro d hd
          change d ∈ (selfDualNestedPairing rho e A B hAB).toLinearMap.ker
          rw [selfDualNestedPairing_ker rho e A B hAB]
          exact hd)
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro y
    obtain ⟨d, rfl⟩ :=
      (nestedSubrepresentation
        (selfDualOrthogonalSubrepresentation rho e B)
        (selfDualOrthogonalSubrepresentation rho e A)
        (selfDualOrthogonalSubrepresentation_antitone rho e hAB)).toSubmodule.mkQ_surjective y
    exact Representation.IntertwiningMap.isIntertwining _ _
      (selfDualNestedPairing rho e A B hAB) g d

theorem selfDualNestedQuotientIntertwiner_injective
    (rho : Representation k G V) (e : rho.Equiv rho.dual)
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    Function.Injective
      (selfDualNestedQuotientIntertwiner rho e A B hAB) := by
  intro x y hxy
  obtain ⟨d, rfl⟩ :=
    (nestedSubrepresentation
      (selfDualOrthogonalSubrepresentation rho e B)
      (selfDualOrthogonalSubrepresentation rho e A)
      (selfDualOrthogonalSubrepresentation_antitone rho e hAB)).toSubmodule.mkQ_surjective x
  obtain ⟨f, rfl⟩ :=
    (nestedSubrepresentation
      (selfDualOrthogonalSubrepresentation rho e B)
      (selfDualOrthogonalSubrepresentation rho e A)
      (selfDualOrthogonalSubrepresentation_antitone rho e hAB)).toSubmodule.mkQ_surjective y
  apply (Submodule.Quotient.eq
    (nestedSubrepresentation
      (selfDualOrthogonalSubrepresentation rho e B)
      (selfDualOrthogonalSubrepresentation rho e A)
      (selfDualOrthogonalSubrepresentation_antitone rho e hAB)).toSubmodule).mpr
  rw [← selfDualNestedPairing_ker rho e A B hAB]
  apply LinearMap.mem_ker.mpr
  change selfDualNestedPairing rho e A B hAB (d - f) = 0
  rw [map_sub, sub_eq_zero]
  exact hxy

theorem selfDualNestedQuotientIntertwiner_surjective
    [FiniteDimensional k V]
    (rho : Representation k G V) (e : rho.Equiv rho.dual)
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    Function.Surjective
      (selfDualNestedQuotientIntertwiner rho e A B hAB) := by
  intro psi
  obtain ⟨d, hd⟩ := selfDualNestedPairing_surjective rho e A B hAB psi
  refine ⟨Submodule.Quotient.mk d, ?_⟩
  exact hd

/-- Equivariant perfect-pairing form of `(B/A)^* ≃ A^⊥/B^⊥`. -/
noncomputable def selfDualNestedQuotientEquiv
    [FiniteDimensional k V]
    (rho : Representation k G V) (e : rho.Equiv rho.dual)
    (A B : Subrepresentation rho) (hAB : A ≤ B) :
    (nestedQuotientRepresentation
      (selfDualOrthogonalSubrepresentation rho e B)
      (selfDualOrthogonalSubrepresentation rho e A)
      (selfDualOrthogonalSubrepresentation_antitone rho e hAB)).Equiv
        (Representation.dual (nestedQuotientRepresentation A B hAB)) :=
  (selfDualNestedQuotientIntertwiner rho e A B hAB).ofBijective
    ⟨selfDualNestedQuotientIntertwiner_injective rho e A B hAB,
      selfDualNestedQuotientIntertwiner_surjective rho e A B hAB⟩

end SymmetricSubgroupAsymptotics

end
