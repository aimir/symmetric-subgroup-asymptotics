import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergPairing
import SymmetricSubgroupAsymptotics.CFSGHeisenbergCentralIsotropy
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! PRIME-field bilinearity of the actual radical commutator, with its
actual signed central parameter space. In particular the half-dimension
bound applies to arbitrary additive central intersections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

def primeCentralSpace (q : CFSG.PrimePower) (s : ℕ) : Submodule (ZMod q.prime) (q.Extension 2) :=
  AddSubgroup.toZModSubmodule q.prime (centralParameters q s)

def primeCentralEquiv (q : CFSG.PrimePower) (s : ℕ) :
    primeCentralSpace q s ≃+ centralParameters q s where
  toFun c := ⟨c.val, c.property⟩
  invFun c := ⟨c.val, c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def primeCentralPair (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin (s + 1) → q.Extension 2) : primeCentralSpace q s :=
  ⟨centralPairParameter q s v w, centralPairParameter_mem q s v w⟩

def primeCentralPairRightHom (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) :
    (Fin (s + 1) → q.Extension 2) →+ primeCentralSpace q s :=
  AddMonoidHom.mk' (primeCentralPair q s v) (fun w z =>
    Subtype.ext (centralPairParameter_add_right q s v w z))

def primeCentralPairLeftHom (q : CFSG.PrimePower) (s : ℕ) :
    (Fin (s + 1) → q.Extension 2) →+
      ((Fin (s + 1) → q.Extension 2) →ₗ[ZMod q.prime] primeCentralSpace q s) :=
  AddMonoidHom.mk' (fun v => (primeCentralPairRightHom q s v).toZModLinearMap q.prime)
    (by
      intro u v
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      exact centralPairParameter_add_left q s u v w)

def primeCentralPairing (q : CFSG.PrimePower) (s : ℕ) :
    (Fin (s + 1) → q.Extension 2) →ₗ[ZMod q.prime]
      ((Fin (s + 1) → q.Extension 2) →ₗ[ZMod q.prime] primeCentralSpace q s) :=
  (primeCentralPairLeftHom q s).toZModLinearMap q.prime

theorem primeCentralPairing_apply (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin (s + 1) → q.Extension 2) :
    (primeCentralPairing q s v w).val = centralPairParameter q s v w := rfl

theorem primeCentralPairing_alternating (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) : primeCentralPairing q s v v = 0 := by
  apply Subtype.ext
  exact congrArg Subtype.val (centralPair_alternating q s v)

theorem primeCentralPairing_surjective (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) (hv : v ≠ 0) :
    Function.Surjective (primeCentralPairing q s v) := by
  intro c
  obtain ⟨w, hw⟩ := centralPair_surjective q s v hv (primeCentralEquiv q s c)
  refine ⟨w, ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val hw

theorem primeVector_finrank (q : CFSG.PrimePower) (s : ℕ) :
    Module.finrank (ZMod q.prime) (Fin (s + 1) → q.Extension 2) =
      2 * ((s + 1) * q.exponent) := by
  rw [Module.finrank_pi_fintype, GaloisField.finrank q.prime
    (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt q.exponent_pos))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (s + 1) * (2 * q.exponent) = 2 * ((s + 1) * q.exponent)
  ring

theorem twice_finrank_le_of_centralPairing (q : CFSG.PrimePower) (s : ℕ)
    (C : AddSubgroup (primeCentralSpace q s)) (hC : C ≠ ⊤)
    (L : AddSubgroup (Fin (s + 1) → q.Extension 2))
    (hL : ∀ v ∈ L, ∀ w ∈ L, primeCentralPairing q s v w ∈ C) :
    Module.finrank (ZMod q.prime) (AddSubgroup.toZModSubmodule q.prime L) ≤
      (s + 1) * q.exponent := by
  have hh := CFSGHeisenbergCentralIsotropy.additive_twice_finrank_le q.prime
    (primeCentralPairing q s) (primeCentralPairing_alternating q s)
    (primeCentralPairing_surjective q s) C hC L hL
  rw [primeVector_finrank] at hh
  omega

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
