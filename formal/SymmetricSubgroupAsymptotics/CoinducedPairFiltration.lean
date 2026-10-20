import SymmetricSubgroupAsymptotics.RepresentationHeadExact
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

/-!
The actual two-layer filtration of a binary induced pair frame.

An actual index-two stabilizer filtration in characteristic two.
H is the point stabilizer, L the pair stabilizer, and sigma is the
extension of the actual local representation to L. The extension is an
input to this algebra lemma; the original pair-kernel argument must supply
it through the actual quotient of the pair stabilizer.

The two-coset fields are literal group identities. There is no assumed
head bound, equivariant splitting, product replacement, or classification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CoinducedPairFiltration

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (H L : Subgroup G) (hHL : H ≤ L)

/-- Explicit two-coset data supplied by the action on the original pair.
A swap need not have order two: its square need only lie in H. -/
structure TwoCosetData where
  swap : L
  inverse_conjugate_mem :
    ∀ h : H, (swap : G)⁻¹ * (h : G) * (swap : G) ∈ H
  square_mem : (swap : G) * (swap : G) ∈ H
  decompose :
    ∀ l : L, ∃ h : H,
      l = Subgroup.inclusion hHL h ∨
      l = swap * Subgroup.inclusion hHL h

variable (sigma : Representation (ZMod 2) L V)

abbrev pointFibre : Representation (ZMod 2) H V :=
  sigma.comp (Subgroup.inclusion hHL)

abbrev pointFrame :=
  Representation.coind H.subtype (pointFibre H L hHL sigma)

abbrev pairFrame :=
  Representation.coind L.subtype sigma

/-- Forget only the stronger L-covariance of the same original function. -/
def inclusion : (pairFrame L sigma).IntertwiningMap
    (pointFrame H L hHL sigma) where
  toLinearMap := {
    toFun f := ⟨f.1, fun h g => f.2 (Subgroup.inclusion hHL h) g⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

theorem inclusion_injective :
    Function.Injective (inclusion H L hHL sigma) := by
  intro f g h
  apply Subtype.ext
  exact congrArg
    (fun f : Representation.coindV H.subtype
      (pointFibre H L hHL sigma) => (f : G → V)) h

variable (D : TwoCosetData H L hHL)

/-- The actual twisted pair sum. The sigma(swap) coefficient is essential:
a swap need not act trivially on the local fibre. -/
def sumValue
    (f : Representation.coindV H.subtype (pointFibre H L hHL sigma))
    (g : G) : V :=
  f.1 g + sigma D.swap (f.1 ((D.swap : G)⁻¹ * g))

private theorem point_covariance
    (f : Representation.coindV H.subtype (pointFibre H L hHL sigma))
    (h : H) (g : G) :
    f.1 ((h : G) * g) =
      sigma (Subgroup.inclusion hHL h) (f.1 g) :=
  f.2 h g

private theorem sumValue_point
    (f : Representation.coindV H.subtype (pointFibre H L hHL sigma))
    (h : H) (g : G) :
    sumValue H L hHL sigma D f ((h : G) * g) =
      sigma (Subgroup.inclusion hHL h)
        (sumValue H L hHL sigma D f g) := by
  let h' : H :=
    ⟨(D.swap : G)⁻¹ * (h : G) * (D.swap : G),
      D.inverse_conjugate_mem h⟩
  have harg :
      (D.swap : G)⁻¹ * ((h : G) * g) =
        (h' : G) * ((D.swap : G)⁻¹ * g) := by
    dsimp [h']
    group
  have hmul :
      D.swap * Subgroup.inclusion hHL h' =
        Subgroup.inclusion hHL h * D.swap := by
    apply Subtype.ext
    change (D.swap : G) *
        ((D.swap : G)⁻¹ * (h : G) * (D.swap : G)) =
      (h : G) * (D.swap : G)
    group
  have hsigma (v : V) :
      sigma D.swap (sigma (Subgroup.inclusion hHL h') v) =
        sigma (Subgroup.inclusion hHL h) (sigma D.swap v) := by
    simpa only [map_mul, Module.End.mul_apply] using
      congrArg (fun l : L => sigma l v) hmul
  change f.1 ((h : G) * g) +
      sigma D.swap (f.1 ((D.swap : G)⁻¹ * ((h : G) * g))) = _
  rw [point_covariance H L hHL sigma, harg,
    point_covariance H L hHL sigma, hsigma]
  exact (map_add (sigma (Subgroup.inclusion hHL h)) _ _).symm

private theorem sumValue_swap
    (f : Representation.coindV H.subtype (pointFibre H L hHL sigma))
    (g : G) :
    sumValue H L hHL sigma D f ((D.swap : G) * g) =
      sigma D.swap (sumValue H L hHL sigma D f g) := by
  let hsq : H := ⟨(D.swap : G) * (D.swap : G), D.square_mem⟩
  have hsqL : Subgroup.inclusion hHL hsq = D.swap * D.swap := rfl
  have hsqCov :=
    point_covariance H L hHL sigma f hsq ((D.swap : G)⁻¹ * g)
  have harg :
      (hsq : G) * ((D.swap : G)⁻¹ * g) =
        (D.swap : G) * g := by
    dsimp [hsq]
    group
  rw [harg, hsqL, map_mul, Module.End.mul_apply] at hsqCov
  simp only [sumValue, inv_mul_cancel_left, map_add]
  rw [← hsqCov]
  exact add_comm _ _

private theorem sumValue_covariance
    (f : Representation.coindV H.subtype (pointFibre H L hHL sigma))
    (l : L) (g : G) :
    sumValue H L hHL sigma D f ((l : G) * g) =
      sigma l (sumValue H L hHL sigma D f g) := by
  obtain ⟨h, hh | hh⟩ := D.decompose l
  · subst l
    exact sumValue_point H L hHL sigma D f h g
  · subst l
    change sumValue H L hHL sigma D f
        (((D.swap : G) * (h : G)) * g) = _
    rw [mul_assoc, sumValue_swap H L hHL sigma D,
      sumValue_point H L hHL sigma D, map_mul, Module.End.mul_apply]

/-- An actual G-intertwiner to the pair-stabilizer-induced module. -/
def pairSum : (pointFrame H L hHL sigma).IntertwiningMap
    (pairFrame L sigma) where
  toLinearMap := {
    toFun f := ⟨sumValue H L hHL sigma D f,
      sumValue_covariance H L hHL sigma D f⟩
    map_add' f g := by
      apply Subtype.ext
      funext x
      simp only [sumValue, Submodule.coe_add, Pi.add_apply, map_add]
      abel
    map_smul' c f := by
      apply Subtype.ext
      funext x
      simp only [sumValue, Submodule.coe_smul, Pi.smul_apply, map_smul,
        smul_add, RingHom.id_apply] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change f.1 (x * g) +
        sigma D.swap (f.1 (((D.swap : G)⁻¹ * x) * g)) =
      f.1 (x * g) +
        sigma D.swap (f.1 ((D.swap : G)⁻¹ * (x * g)))
    rw [mul_assoc]

private theorem binary_add_self (v : V) : v + v = 0 := by
  calc
    v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by
      have htwo : (1 : ZMod 2) + 1 = 0 := by decide +kernel
      rw [htwo, zero_smul]

/-- No choice of a splitting is needed: the pair sum kills the diagonal. -/
theorem pairSum_inclusion
    (f : Representation.coindV L.subtype sigma) :
    pairSum H L hHL sigma D (inclusion H L hHL sigma f) = 0 := by
  apply Subtype.ext
  funext g
  change f.1 g + sigma D.swap
    (f.1 ((D.swap : G)⁻¹ * g)) = 0
  have hcov := f.2 D.swap⁻¹ g
  change f.1 ((D.swap : G)⁻¹ * g) = sigma D.swap⁻¹ (f.1 g) at hcov
  rw [hcov]
  have hcancel (v : V) : sigma D.swap (sigma D.swap⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hcancel]
  exact binary_add_self _

/-- Exactness is equality of the literal ambient range and kernel.
This remains useful after restricting pairSum to any correlated submodule;
one must then use its actual image, not assert restricted surjectivity. -/
theorem inclusion_range_eq_pairSum_kernel :
    (inclusion H L hHL sigma).toLinearMap.range =
      (pairSum H L hHL sigma D).toLinearMap.ker := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact pairSum_inclusion H L hHL sigma D f
  · intro f hf
    have hzero (g : G) :
        sumValue H L hHL sigma D f g = 0 :=
      congrFun (congrArg Subtype.val hf) g
    have hswap (g : G) :
        f.1 ((D.swap : G) * g) = sigma D.swap (f.1 g) := by
      have h := hzero ((D.swap : G) * g)
      simp only [sumValue, inv_mul_cancel_left] at h
      calc
        f.1 ((D.swap : G) * g) =
            f.1 ((D.swap : G) * g) +
              (sigma D.swap (f.1 g) + sigma D.swap (f.1 g)) := by
                rw [binary_add_self, add_zero]
        _ = (f.1 ((D.swap : G) * g) +
              sigma D.swap (f.1 g)) + sigma D.swap (f.1 g) := by abel
        _ = sigma D.swap (f.1 g) := by rw [h, zero_add]
    have hcov : ∀ (l : L) (g : G),
        f.1 ((l : G) * g) = sigma l (f.1 g) := by
      intro l g
      obtain ⟨h, hh | hh⟩ := D.decompose l
      · subst l
        exact point_covariance H L hHL sigma f h g
      · subst l
        change f.1 (((D.swap : G) * (h : G)) * g) = _
        rw [mul_assoc, hswap, point_covariance H L hHL sigma,
          map_mul, Module.End.mul_apply]
    exact ⟨⟨f.1, hcov⟩, rfl⟩

/-- Restrict the literal pair sum to the correlated source itself. -/
def subrepresentationPairSum
    (B : Subrepresentation (pointFrame H L hHL sigma)) :
    B.toRepresentation.IntertwiningMap (pairFrame L sigma) where
  toLinearMap := (pairSum H L hHL sigma D).toLinearMap.comp
    B.toSubmodule.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro b
    exact Representation.IntertwiningMap.isIntertwining _ _
      (pairSum H L hHL sigma D) g b.1

/-- The restricted map need not be onto the pair frame. Its literal
kernel and image are the two terms used by exact-head subadditivity. -/
theorem correlated_head_le_kernel_add_range
    [Finite G] [FiniteDimensional (ZMod 2) V]
    (B : Subrepresentation (pointFrame H L hHL sigma)) :
    Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) G (ZMod 2))) ≤
      Module.finrank (ZMod 2)
        ((subrepresentationPairSum H L hHL sigma D B).ker.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) G (ZMod 2))) +
      Module.finrank (ZMod 2)
        ((subrepresentationPairSum H L hHL sigma D B).range.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) G (ZMod 2))) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional (ZMod 2) (G → V) := inferInstance
  letI : FiniteDimensional (ZMod 2)
      (Representation.coindV H.subtype (pointFibre H L hHL sigma)) :=
    FiniteDimensional.of_injective
      (Representation.coindV H.subtype (pointFibre H L hHL sigma)).subtype
      (Representation.coindV H.subtype (pointFibre H L hHL sigma)).subtype_injective
  letI : FiniteDimensional (ZMod 2) (Representation.coindV L.subtype sigma) :=
    FiniteDimensional.of_injective
      (Representation.coindV L.subtype sigma).subtype
      (Representation.coindV L.subtype sigma).subtype_injective
  letI : FiniteDimensional (ZMod 2) B.toSubmodule :=
    FiniteDimensional.of_injective B.toSubmodule.subtype B.toSubmodule.subtype_injective
  exact RepresentationHeadExact.head_finrank_le_kernel_add_range
    (k := ZMod 2) (G := G) (V := B.toSubmodule)
    (W := Representation.coindV L.subtype sigma)
    (ρ := B.toRepresentation) (σ := pairFrame L sigma)
    (subrepresentationPairSum H L hHL sigma D B)

end SymmetricSubgroupAsymptotics.CoinducedPairFiltration

end
