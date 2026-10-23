import SymmetricSubgroupAsymptotics.CFSGQuadraticFixedSpanDescent
import SymmetricSubgroupAsymptotics.CFSGTwistedDDisplacementScalarSpan
import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace

/-! Honest base/extension-field span descent on the actual defining-fixed
quadratic carrier. Membership, order and intersections are retained;
the original fixed-F planes are not replaced by ambient K-planes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedScalarSpanDescent
open CFSGOrthogonalDSerreMatrices CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDDisplacementScalarSpan
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists

def definingVectorSemilinear (n : ℕ) (q : CFSG.PrimePower) :
    (Index (n + 2) → q.Extension 2) →ₛₗ[(definingFieldAutomorphism q 2).toRingHom]
      (Index (n + 2) → q.Extension 2) where
  toFun := vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2)
  map_add' v w := by
    funext i
    change definingFieldAutomorphism q 2 (_ + _) = _ + _
    exact map_add _ _ _
  map_smul' a v := by
    funext i
    change definingFieldAutomorphism q 2 (a * _) = definingFieldAutomorphism q 2 a * _
    exact map_mul _ _ _

def underlyingFixedSubmodule (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q)) :
    Submodule (fixedField q) (Index (n + 2) → q.Extension 2) :=
  P.map (fixedSpace n q).subtype

theorem underlying_fixed (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q))
    (x : Index (n + 2) → q.Extension 2) (hx : x ∈ underlyingFixedSubmodule n q P) :
    definingVectorSemilinear n q x = x := by
  obtain ⟨v, _, rfl⟩ := hx
  exact v.property

theorem underlying_mem_iff (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q)) (x : fixedSpace n q) :
    x.val ∈ underlyingFixedSubmodule n q P ↔ x ∈ P := by
  constructor
  · rintro ⟨v, hv, he⟩
    have hx : v = x := Subtype.ext he
    exact hx ▸ hv
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem scalarSpan_eq_underlying_span (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q)) :
    scalarSpan n q P = Submodule.span (q.Extension 2) (underlyingFixedSubmodule n q P : Set _) := rfl

theorem fixed_mem_scalarSpan_iff (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q)) (x : fixedSpace n q) :
    x.val ∈ scalarSpan n q P ↔ x ∈ P := by
  obtain ⟨theta, htheta⟩ := CFSGTwistedAQuadraticTrace.exists_nonfixed q
  rw [scalarSpan_eq_underlying_span]
  exact (CFSGQuadraticFixedSpanDescent.fixed_mem_span_iff
    (definingFieldAutomorphism q 2) theta htheta (fixedField q)
    (fun a => CFSGTwistedANaturalMatrices.extension_two_pow_twice q a) (fun _ => Iff.rfl)
    (definingVectorSemilinear n q) (underlyingFixedSubmodule n q P)
    (underlying_fixed n q P) x.val x.property).trans (underlying_mem_iff n q P x)

theorem scalarSpan_le_iff (n : ℕ) (q : CFSG.PrimePower)
    (P Q : Submodule (fixedField q) (fixedSpace n q)) :
    scalarSpan n q P ≤ scalarSpan n q Q ↔ P ≤ Q := by
  constructor
  · intro h x hx
    apply (fixed_mem_scalarSpan_iff n q Q x).mp
    exact h ((fixed_mem_scalarSpan_iff n q P x).mpr hx)
  · intro h
    exact Submodule.span_mono (Set.image_mono h)

theorem scalarSpan_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (scalarSpan n q) := by
  intro P Q h
  exact le_antisymm ((scalarSpan_le_iff n q P Q).mp h.le)
    ((scalarSpan_le_iff n q Q P).mp h.ge)

theorem underlying_inf (n : ℕ) (q : CFSG.PrimePower)
    (P Q : Submodule (fixedField q) (fixedSpace n q)) :
    underlyingFixedSubmodule n q (P ⊓ Q) =
      underlyingFixedSubmodule n q P ⊓ underlyingFixedSubmodule n q Q := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv.1, rfl⟩, ⟨v, hv.2, rfl⟩⟩
  · rintro ⟨⟨v, hv, he⟩, ⟨w, hw, he'⟩⟩
    have hvw : v = w := Subtype.ext (he.trans he'.symm)
    exact ⟨v, ⟨hv, hvw.symm ▸ hw⟩, he⟩

theorem scalarSpan_inf (n : ℕ) (q : CFSG.PrimePower)
    (P Q : Submodule (fixedField q) (fixedSpace n q)) :
    scalarSpan n q (P ⊓ Q) = scalarSpan n q P ⊓ scalarSpan n q Q := by
  obtain ⟨theta, htheta⟩ := CFSGTwistedAQuadraticTrace.exists_nonfixed q
  rw [scalarSpan_eq_underlying_span, scalarSpan_eq_underlying_span, scalarSpan_eq_underlying_span, underlying_inf]
  exact CFSGQuadraticFixedSpanDescent.span_inf (definingFieldAutomorphism q 2) theta htheta (fixedField q)
    (fun a => CFSGTwistedANaturalMatrices.extension_two_pow_twice q a) (fun _ => Iff.rfl)
    (definingVectorSemilinear n q) (underlyingFixedSubmodule n q P) (underlyingFixedSubmodule n q Q)
    (underlying_fixed n q P) (underlying_fixed n q Q)

theorem scalarSpan_bot (n : ℕ) (q : CFSG.PrimePower) :
    scalarSpan n q ⊥ = ⊥ := by
  unfold scalarSpan
  have he : (fun x : fixedSpace n q => x.val) ''
      (↑(⊥ : Submodule (fixedField q) (fixedSpace n q)) : Set (fixedSpace n q)) = {0} := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hz : v = 0 := hv
      simp only [hz, Submodule.coe_zero, Set.mem_singleton_iff]
    · rintro rfl
      exact ⟨0, Submodule.zero_mem _, rfl⟩
  rw [he, Submodule.span_singleton_eq_bot.mpr rfl]

theorem scalarSpan_disjoint_iff (n : ℕ) (q : CFSG.PrimePower)
    (P Q : Submodule (fixedField q) (fixedSpace n q)) :
    Disjoint (scalarSpan n q P) (scalarSpan n q Q) ↔ Disjoint P Q := by
  rw [disjoint_iff, disjoint_iff, ← scalarSpan_inf, ← scalarSpan_bot n q]
  exact (scalarSpan_injective n q).eq_iff

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedScalarSpanDescent
