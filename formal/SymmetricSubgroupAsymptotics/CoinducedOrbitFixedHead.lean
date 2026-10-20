import SymmetricSubgroupAsymptotics.InducedDoubleCosetIndices
import SymmetricSubgroupAsymptotics.OddNormalizerSubrepresentationHead
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
The fixed vectors of an actual coinduced frame are detected by evaluation
on its actual double cosets. The value at a representative belongs to the
fixed space of the original, conjugation-twisted local stabilizer action.

This proves the orbitwise bound used in the structural sixteen-point
branches without enumerating submodules or replacing the local action by
an untwisted permutation module. Coprime averaging then applies to every
actual ambient subrepresentation. Orbit counts and vanishing of particular
local fixed spaces remain geometric facts to be proved by callers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.CoinducedOrbitFixedHead

variable {k G V : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  (H P : Subgroup G) (rho : Representation k H V)

abbrev fixedSpace :=
  Representation.invariants ((Representation.coind H.subtype rho).comp P.subtype)

abbrev fibreFixedSpace
    (q : DoubleCoset.Quotient (H : Set G) (P : Set G)) :=
  Representation.invariants (inducedOrbitFibre H P rho q.out)

theorem fixed_value_mul (f : fixedSpace H P rho) (x : G) (p : P) :
    f.1.1 (x * (p : G)) = f.1.1 x := by
  have hp := f.2 p
  exact congrArg (fun v : Representation.coindV H.subtype rho => v.1 x) hp

theorem value_mem_fibreFixedSpace
    (f : fixedSpace H P rho)
    (q : DoubleCoset.Quotient (H : Set G) (P : Set G)) :
    f.1.1 q.out ∈ fibreFixedSpace H P rho q := by
  intro l
  change rho (inducedOrbitTwist H P q.out l) (f.1.1 q.out) = f.1.1 q.out
  calc
    _ = f.1.1 ((inducedOrbitTwist H P q.out l : G) * q.out) :=
      (f.1.2 (inducedOrbitTwist H P q.out l) q.out).symm
    _ = f.1.1 (q.out * ((l : P) : G)) := by
      apply congrArg f.1.1
      change (q.out * ((l : P) : G) * q.out⁻¹) * q.out = _
      group
    _ = f.1.1 q.out := fixed_value_mul H P rho f q.out (l : P)

/-- Evaluation retains the actual fixed fibre for each original double
coset, including its conjugation twist. -/
def evaluation : fixedSpace H P rho →ₗ[k]
    (∀ q : DoubleCoset.Quotient (H : Set G) (P : Set G),
      fibreFixedSpace H P rho q) where
  toFun f q := ⟨f.1.1 q.out, value_mem_fibreFixedSpace H P rho f q⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluation_injective : Function.Injective (evaluation H P rho) := by
  intro f f' he
  apply Subtype.ext
  apply Subtype.ext
  funext x
  let q : DoubleCoset.Quotient (H : Set G) (P : Set G) := DoubleCoset.mk H P x
  have hq : DoubleCoset.mk H P q.out = DoubleCoset.mk H P x :=
    DoubleCoset.out_eq' H P q
  obtain ⟨h, hh, p, hp, hx⟩ := (DoubleCoset.eq H P q.out x).mp hq
  have hv := congrArg
    (fun v : (∀ q : DoubleCoset.Quotient (H : Set G) (P : Set G),
      fibreFixedSpace H P rho q) => (v q : V)) he
  change f.1.1 q.out = f'.1.1 q.out at hv
  have hvp : f.1.1 (q.out * p) = f'.1.1 (q.out * p) :=
    (fixed_value_mul H P rho f q.out (⟨p, hp⟩ : P)).trans
      (hv.trans (fixed_value_mul H P rho f' q.out (⟨p, hp⟩ : P)).symm)
  rw [hx, mul_assoc]
  exact (f.1.2 ⟨h, hh⟩ (q.out * p)).trans
    ((congrArg (rho ⟨h, hh⟩) hvp).trans (f'.1.2 ⟨h, hh⟩ (q.out * p)).symm)

variable [Finite G] [FiniteDimensional k V]
  [Fintype (DoubleCoset.Quotient (H : Set G) (P : Set G))]

omit [Finite G] in
/-- The full fixed-space bound is the sum of the exact twisted-fibre
fixed ranks. No geometric vanishing or orbit-count premise is inserted. -/
theorem fixed_finrank_le_sum :
    Module.finrank k (fixedSpace H P rho) ≤
      ∑ q : DoubleCoset.Quotient (H : Set G) (P : Set G),
        Module.finrank k (fibreFixedSpace H P rho q) := by
  exact (LinearMap.finrank_le_finrank_of_injective
    (f := evaluation H P rho) (evaluation_injective H P rho)).trans_eq
      (Module.finrank_pi_fintype k)

omit [Fintype (DoubleCoset.Quotient (H : Set G) (P : Set G))] in
/-- The averaging step is proved on an arbitrary carrier, before any
coinduced carrier is substituted. -/
theorem subrepresentation_head_le_fixed
    (sigma : Representation k G V)
    (hP : IsUnit (Nat.card P : k)) (B : Subrepresentation sigma) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      Module.finrank k (Representation.invariants (sigma.comp P.subtype)) := by
  have hfixed : oddNormalizerFixedSpace sigma P (1 : G) =
      Representation.invariants (sigma.comp P.subtype) := by
    apply le_antisymm inf_le_left
    intro v hv
    refine ⟨hv, ?_⟩
    apply (mem_representationElementFixedSpace _ _ _).mpr
    simp only [map_one, Module.End.one_apply]
  have h := subrepresentation_coinvariants_le_oddNormalizerFixedSpace
    (ρ := sigma) (A := P) (g := (1 : G)) hP (Subgroup.one_mem _) B
  rw [hfixed] at h
  exact (representationHead_finrank_eq_coinvariants B.toRepresentation).le.trans h

/-- Coprime averaging bounds every actual subrepresentation head by the
same actual orbit sum. -/
theorem subrepresentation_head_le_sum
    (hP : IsUnit (Nat.card P : k))
    (B : Subrepresentation (Representation.coind H.subtype rho)) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      ∑ q : DoubleCoset.Quotient (H : Set G) (P : Set G),
        Module.finrank k (fibreFixedSpace H P rho q) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional k (Representation.coindV H.subtype rho) :=
    FiniteDimensional.of_injective
      (Representation.coindV H.subtype rho).subtype
      (Representation.coindV H.subtype rho).subtype_injective
  have h : Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
        Module.finrank k (fixedSpace H P rho) :=
    subrepresentation_head_le_fixed (V := Representation.coindV H.subtype rho)
      P (Representation.coind H.subtype rho) hP B
  exact h.trans (fixed_finrank_le_sum H P rho)

/-- A sparse form of the same bound. A zero entry must be established on
the actual twisted local fixed space, not inferred from an orbit label. -/
theorem subrepresentation_head_le_active
    (hP : IsUnit (Nat.card P : k))
    (active : Finset (DoubleCoset.Quotient (H : Set G) (P : Set G)))
    (inactive : ∀ q, q ∉ active → fibreFixedSpace H P rho q = ⊥)
    (B : Subrepresentation (Representation.coind H.subtype rho)) :
    Module.finrank k
      (B.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
      active.card * Module.finrank k V := by
  apply (subrepresentation_head_le_sum H P rho hP B).trans
  calc
    _ = ∑ q ∈ active, Module.finrank k (fibreFixedSpace H P rho q) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ active)
      intro q _ hq
      rw [inactive q hq, finrank_bot]
    _ ≤ ∑ _q ∈ active, Module.finrank k V := by
      exact Finset.sum_le_sum (fun q _ => Submodule.finrank_le _)
    _ = active.card * Module.finrank k V := by simp

end SymmetricSubgroupAsymptotics.CoinducedOrbitFixedHead

end
