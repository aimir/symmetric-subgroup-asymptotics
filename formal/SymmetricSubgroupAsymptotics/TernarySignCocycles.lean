import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.GroupTheory.PGroup
import Mathlib.FieldTheory.Finiteness

/-!
# Exact cocycles of an original nontrivial ternary sign module

The source is the stated binary group B, and the representation is its
stated actual scalar sign action. Every cocycle vanishes on the sign kernel:
its values there are killed by both a power of two and characteristic three.
Evaluation at one original element of nontrivial sign then identifies the
whole cocycle space with the original module, with explicit principal inverse.

No finiteness of B, averaging, extension splitting, or assumed cohomology
vanishing is used. In a repeated-marker application B must be the actual
binary contraction image with the original action factored through it;
the generally nonbinary original marker subgroup is not a valid substitute.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernarySignCocycles

open groupCohomology OddMarkerTernaryChart

variable {B : Type} [Group B] (A : Rep (ZMod 3) B)
    (χ : B →* Multiplicative (ZMod 2))
    (hρ : ∀ b v, A.ρ b v = signScalar (χ b) • v)

include hρ in
/-- Restricted to the actual sign kernel, the cocycle has the ordinary
power formula of a homomorphism into the additive module. -/
theorem cocycle_kernel_power (z : cocycles₁ A) (b : B) (hb : χ b = 1) (n : ℕ) :
    z (b^n) = n • z b := by
  induction n with
  | zero => simp only [pow_zero, cocycles₁_map_one, zero_smul]
  | succ n ih =>
      rw [pow_succ, (mem_cocycles₁_iff z).mp z.2, hρ, map_pow, hb, one_pow,
        signScalar_one, one_smul, ih, succ_nsmul]
      exact add_comm _ _

include hρ in
/-- This uses only the power-of-two order of this particular source
element. The whole binary source need not be finite. -/
theorem cocycle_kills_sign_kernel (hB : IsPGroup 2 B) (z : cocycles₁ A)
    (b : B) (hb : χ b = 1) : z b = 0 := by
  obtain ⟨r, hr⟩ := hB b
  have hp := cocycle_kernel_power A χ hρ z b hb (2^r)
  rw [hr, cocycles₁_map_one] at hp
  have hs : ((2 : ZMod 3)^r) • z b = 0 := by
    have hc : ((2^r : ℕ) : ZMod 3) = (2 : ZMod 3)^r := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [← hc, Nat.cast_smul_eq_nsmul]
    exact hp.symm
  exact (smul_eq_zero.mp hs).resolve_left (pow_ne_zero _ (by decide : (2 : ZMod 3) ≠ 0))

private theorem minus_one_smul_sub (v : A) : (-1 : ZMod 3) • v - v = v := by
  calc
    (-1 : ZMod 3) • v - v = ((-1 : ZMod 3) - 1) • v := by
      rw [sub_smul, one_smul]
    _ = v := by
      rw [show (-1 : ZMod 3) - 1 = 1 by decide, one_smul]

include hρ in
/-- A cocycle is the principal cocycle of its value at the actual odd
element. The parameter sign and action are those of the original B. -/
theorem cocycle_principal (hB : IsPGroup 2 B) (s : B)
    (hs : χ s = Multiplicative.ofAdd (1 : ZMod 2))
    (z : cocycles₁ A) (b : B) : z b = A.ρ b (z s) - z s := by
  have hcases : ∀ t : Multiplicative (ZMod 2),
      t = 1 ∨ t = Multiplicative.ofAdd (1 : ZMod 2) := by decide +kernel
  rcases hcases (χ b) with hb | hb
  · rw [cocycle_kills_sign_kernel A χ hρ hB z b hb, hρ, hb,
      signScalar_one, one_smul, sub_self]
  · have hk : χ (s⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hs, hb, inv_mul_cancel]
    have hz : z (s⁻¹ * b) = 0 := cocycle_kills_sign_kernel A χ hρ hB z _ hk
    have he := (mem_cocycles₁_iff z).mp z.2 s (s⁻¹ * b)
    simp only [mul_inv_cancel_left, hz, map_zero, zero_add] at he
    rw [he, hρ, hb, signScalar_nontrivial]
    exact (minus_one_smul_sub A (z s)).symm

/-- The actual degree-zero differential, with its value retained as a
literal one-cocycle in mathlib's original representation. -/
def principalMap : A →ₗ[ZMod 3] cocycles₁ A :=
  (d₀₁ A).hom.codRestrict (cocycles₁ A) (fun v => d₀₁_apply_mem_cocycles₁ v)

@[simp] theorem principalMap_apply (v : A) (b : B) :
    principalMap A v b = A.ρ b v - v := rfl

def evaluation (s : B) : cocycles₁ A →ₗ[ZMod 3] A where
  toFun z := z s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hρ in
theorem principal_evaluation (s : B)
    (hs : χ s = Multiplicative.ofAdd (1 : ZMod 2)) (v : A) :
    evaluation A s (principalMap A v) = v := by
  change A.ρ s v - v = v
  rw [hρ, hs, signScalar_nontrivial]
  exact minus_one_smul_sub A v

include hρ in
theorem evaluation_principal (hB : IsPGroup 2 B) (s : B)
    (hs : χ s = Multiplicative.ofAdd (1 : ZMod 2)) (z : cocycles₁ A) :
    principalMap A (evaluation A s z) = z := by
  apply cocycles₁_ext
  intro b
  exact (cocycle_principal A χ hρ hB s hs z b).symm

/-- A genuine linear equivalence given by evaluation on the original
source. Its inverse is exactly the principal-cocycle map. -/
def evaluationEquiv (hB : IsPGroup 2 B) (s : B)
    (hs : χ s = Multiplicative.ofAdd (1 : ZMod 2)) : cocycles₁ A ≃ₗ[ZMod 3] A where
  toLinearMap := evaluation A s
  invFun := principalMap A
  left_inv := evaluation_principal A χ hρ hB s hs
  right_inv := principal_evaluation A χ hρ s hs

@[simp] theorem evaluationEquiv_apply (hB : IsPGroup 2 B) (s : B)
    (hs : χ s = Multiplicative.ofAdd (1 : ZMod 2)) (z : cocycles₁ A) :
    evaluationEquiv A χ hρ hB s hs z = z s := rfl

@[simp] theorem evaluationEquiv_symm_apply (hB : IsPGroup 2 B) (s : B)
    (hs : χ s = Multiplicative.ofAdd (1 : ZMod 2)) (v : A) :
    (evaluationEquiv A χ hρ hB s hs).symm v = principalMap A v := rfl

include hρ in
theorem cocycles_card (hB : IsPGroup 2 B) (s : B)
    (hs : χ s = Multiplicative.ofAdd (1 : ZMod 2)) :
    Nat.card (cocycles₁ A) = Nat.card A :=
  Nat.card_congr (evaluationEquiv A χ hρ hB s hs).toEquiv

include hρ in
theorem cocycles_card_pow [FiniteDimensional (ZMod 3) A]
    (hB : IsPGroup 2 B) (s : B)
    (hs : χ s = Multiplicative.ofAdd (1 : ZMod 2)) :
    Nat.card (cocycles₁ A) = 3 ^ Module.finrank (ZMod 3) A := by
  rw [cocycles_card A χ hρ hB s hs, Module.natCard_eq_pow_finrank (K := ZMod 3)]
  rw [Nat.card_zmod]

/-- Nontriviality supplies a genuine odd source element, without a
finite enumeration of B or a chosen abstract C2 replacement. -/
theorem exists_nontrivial_sign (hχ : χ ≠ 1) :
    ∃ s : B, χ s = Multiplicative.ofAdd (1 : ZMod 2) := by
  by_contra h
  apply hχ
  apply MonoidHom.ext
  intro s
  have hcases : ∀ t : Multiplicative (ZMod 2),
      t = 1 ∨ t = Multiplicative.ofAdd (1 : ZMod 2) := by decide +kernel
  exact (hcases (χ s)).resolve_right (fun hs => h ⟨s, hs⟩)

include hρ in
theorem cocycles_card_of_nontrivial (hB : IsPGroup 2 B) (hχ : χ ≠ 1) :
    Nat.card (cocycles₁ A) = Nat.card A := by
  obtain ⟨s, hs⟩ := exists_nontrivial_sign χ hχ
  exact cocycles_card A χ hρ hB s hs

end SymmetricSubgroupAsymptotics.TernarySignCocycles

end
