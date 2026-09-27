import SymmetricSubgroupAsymptotics.TernarySignCocycles

/-!
# Exact cocycles from a finite resolution by original sign components

A finite family of linear maps summing to the identity suffices. Both
orders of composition with the actual action are retained, and each
component has its own actual nontrivial sign. The inverse to the principal
cocycle map is the sum of projected evaluations at actual odd elements.

No independence of original coordinates, finite source, product-module
identification, or numerical cocycle-count premise is used. In particular,
one may use the distinct-sign projections on an invariant quotient.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.TernarySignResolution

open groupCohomology OddMarkerTernaryChart TernarySignCocycles

variable {B : Type} [Group B] (A : Rep (ZMod 3) B)

/-- The scalar action used only to read one projected cocycle. Its
underlying module remains the same actual module A. -/
def scalarRepresentation (χ : B →* Multiplicative (ZMod 2)) :
    Representation (ZMod 3) B A where
  toFun b := signScalar (χ b) • LinearMap.id
  map_one' := by
    ext v
    simp
  map_mul' b c := by
    ext v
    change signScalar (χ (b*c)) • v =
      signScalar (χ b) • (signScalar (χ c) • v)
    rw [map_mul, signScalar_mul, mul_smul]

abbrev scalarRep (χ : B →* Multiplicative (ZMod 2)) : Rep (ZMod 3) B :=
  Rep.of (scalarRepresentation A χ)

def projectedCocycle (χ : B →* Multiplicative (ZMod 2)) (p : A →ₗ[ZMod 3] A)
    (hp : ∀ b v, p (A.ρ b v) = signScalar (χ b) • p v)
    (z : cocycles₁ A) : cocycles₁ (scalarRep A χ) :=
  ⟨fun b => p (z b), by
    apply (mem_cocycles₁_iff _).mpr
    intro b c
    change p (z (b*c)) = signScalar (χ b) • p (z c) + p (z b)
    rw [(mem_cocycles₁_iff z).mp z.2, map_add, hp]⟩

theorem projected_principal (hB : IsPGroup 2 B)
    (χ : B →* Multiplicative (ZMod 2)) (p : A →ₗ[ZMod 3] A)
    (hp : ∀ b v, p (A.ρ b v) = signScalar (χ b) • p v)
    (s : B) (hs : χ s = Multiplicative.ofAdd (1 : ZMod 2))
    (z : cocycles₁ A) (b : B) :
    p (z b) = signScalar (χ b) • p (z s) - p (z s) :=
  cocycle_principal (scalarRep A χ) χ (fun _ _ => rfl) hB s hs
    (projectedCocycle A χ p hp z) b

variable {ι : Type} [Fintype ι]
    (χ : ι → B →* Multiplicative (ZMod 2)) (p : ι → A →ₗ[ZMod 3] A)

/-- Each actual sign chooses its own actual odd element. The sum is
over the supplied resolution, not over repeated physical coordinates. -/
def reconstruction (s : ι → B) : cocycles₁ A →ₗ[ZMod 3] A :=
  ∑ i, (p i).comp (evaluation A (s i))

@[simp] theorem reconstruction_apply (s : ι → B) (z : cocycles₁ A) :
    reconstruction A p s z = ∑ i, p i (z (s i)) := by
  simp [reconstruction, evaluation]

theorem principal_reconstruction (hB : IsPGroup 2 B)
    (hleft : ∀ i b v, p i (A.ρ b v) = signScalar (χ i b) • p i v)
    (hright : ∀ i b v, A.ρ b (p i v) = signScalar (χ i b) • p i v)
    (hsum : ∀ v, ∑ i, p i v = v)
    (s : ι → B) (hs : ∀ i, χ i (s i) = Multiplicative.ofAdd (1 : ZMod 2))
    (z : cocycles₁ A) : principalMap A (reconstruction A p s z) = z := by
  apply cocycles₁_ext
  intro b
  rw [principalMap_apply, reconstruction_apply, map_sum, ← Finset.sum_sub_distrib]
  calc
    (∑ i, ((A.ρ b) (p i (z (s i))) - p i (z (s i)))) = ∑ i, p i (z b) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hright]
      exact (projected_principal A hB (χ i) (p i) (hleft i) (s i) (hs i) z b).symm
    _ = z b := hsum (z b)

theorem reconstruction_principal
    (hleft : ∀ i b v, p i (A.ρ b v) = signScalar (χ i b) • p i v)
    (hsum : ∀ v, ∑ i, p i v = v)
    (s : ι → B) (hs : ∀ i, χ i (s i) = Multiplicative.ofAdd (1 : ZMod 2))
    (v : A) : reconstruction A p s (principalMap A v) = v := by
  rw [reconstruction_apply]
  calc
    (∑ i, p i (principalMap A v (s i))) = ∑ i, p i v := by
      apply Finset.sum_congr rfl
      intro i _
      rw [principalMap_apply, map_sub, hleft, hs, signScalar_nontrivial]
      calc
        (-1 : ZMod 3) • p i v - p i v = ((-1 : ZMod 3)-1) • p i v := by
          rw [sub_smul, one_smul]
        _ = p i v := by rw [show (-1 : ZMod 3)-1=1 by decide, one_smul]
    _ = v := hsum v

/-- Exact original-module cocycle equivalence. Neither orthogonality
nor idempotence is needed beyond the stated resolution equations. -/
def principalEquiv (hB : IsPGroup 2 B)
    (hleft : ∀ i b v, p i (A.ρ b v) = signScalar (χ i b) • p i v)
    (hright : ∀ i b v, A.ρ b (p i v) = signScalar (χ i b) • p i v)
    (hsum : ∀ v, ∑ i, p i v = v)
    (s : ι → B) (hs : ∀ i, χ i (s i) = Multiplicative.ofAdd (1 : ZMod 2)) :
    A ≃ₗ[ZMod 3] cocycles₁ A where
  toLinearMap := principalMap A
  invFun := reconstruction A p s
  left_inv := reconstruction_principal A χ p hleft hsum s hs
  right_inv := principal_reconstruction A χ p hB hleft hright hsum s hs

theorem cocycles_card (hB : IsPGroup 2 B)
    (hleft : ∀ i b v, p i (A.ρ b v) = signScalar (χ i b) • p i v)
    (hright : ∀ i b v, A.ρ b (p i v) = signScalar (χ i b) • p i v)
    (hsum : ∀ v, ∑ i, p i v = v) (hχ : ∀ i, χ i ≠ 1) :
    Nat.card (cocycles₁ A) = Nat.card A := by
  choose s hs using fun i => exists_nontrivial_sign (χ i) (hχ i)
  exact (Nat.card_congr (principalEquiv A χ p hB hleft hright hsum s hs).toEquiv).symm

end SymmetricSubgroupAsymptotics.TernarySignResolution

end
