import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance
import Mathlib.GroupTheory.PGroup

/-! A ternary subgroup of an actual eight-pair action fixes at least four
original points. The pair action has at least two fixed pairs by the
p-group congruence, and its action on either fixed binary fibre is trivial.
No transitivity, kernel independence, or catalogue hypothesis is needed. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPairTernaryFixedPoints

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I) (P : Subgroup U)

abbrev fixedPairs := {i : I // ∀ p : P, F.top (p : U) i = i}

private theorem offset_mul (u v : U) (i : I) :
    F.offset (u * v) i = F.offset v i + F.offset u (F.top v i) := by
  change (F.frame.symm ((u : Equiv.Perm X)
    ((v : Equiv.Perm X) (F.frame (i, 0))))).2 = _
  rw [F.action_frame, F.action_coordinates]
  simp only [zero_add]

/-- The actual offset on a fixed physical pair, as a homomorphism. -/
def fixedPairOffset (i : fixedPairs F P) : P →* Multiplicative (ZMod 2) where
  toFun p := Multiplicative.ofAdd (F.offset (p : U) i.1)
  map_one' := by
    change Multiplicative.ofAdd ((F.frame.symm (F.frame (i.1, 0))).2) = 1
    rw [F.frame.symm_apply_apply]
    rfl
  map_mul' p q := by
    change Multiplicative.ofAdd (F.offset ((p : U) * (q : U)) i.1) =
      Multiplicative.ofAdd (F.offset (p : U) i.1 + F.offset (q : U) i.1)
    rw [offset_mul, i.2 q, add_comm]

theorem fixedPairOffset_eq_one (hP : IsPGroup 3 P)
    (i : fixedPairs F P) (p : P) : fixedPairOffset F P i p = 1 := by
  have hsquare : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 := by decide +kernel
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (hP.orderOf_coprime (by decide) p)
    (orderOf_map_dvd (fixedPairOffset F P i) p)
    (orderOf_dvd_of_pow_eq_one (hsquare _))

theorem fixed_pair_point (hP : IsPGroup 3 P) (i : fixedPairs F P)
    (b : ZMod 2) (p : P) : p • F.frame (i.1, b) = F.frame (i.1, b) := by
  have hoffset : F.offset (p : U) i.1 = 0 :=
    congrArg Multiplicative.toAdd (fixedPairOffset_eq_one F P hP i p)
  change ((p : U) : Equiv.Perm X) (F.frame (i.1, b)) = _
  rw [F.action_frame, i.2 p, hoffset, add_zero]

/-- The two points of every fixed pair are distinct original fixed points. -/
def fixedPointsEmbedding (hP : IsPGroup 3 P) :
    fixedPairs F P × ZMod 2 ↪ MulAction.fixedPoints P X where
  toFun z := ⟨F.frame (z.1.1, z.2), fun p => fixed_pair_point F P hP z.1 z.2 p⟩
  inj' := by
    intro a b h
    have he := F.frame.injective (congrArg (fun x : MulAction.fixedPoints P X => (x : X)) h)
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun z : I × ZMod 2 => z.1) he)
    · exact congrArg (fun z : I × ZMod 2 => z.2) he

theorem two_le_card_fixedPairs [Finite I]
    (hP : IsPGroup 3 P) (hI : Nat.card I = 8) :
    2 ≤ Nat.card (fixedPairs F P) := by
  letI : MulAction P I := MulAction.compHom I (F.top.comp P.subtype)
  have h := hP.card_modEq_card_fixedPoints I
  change Nat.card I % 3 = Nat.card (fixedPairs F P) % 3 at h
  rw [hI] at h
  omega

include F in
/-- This is the original sixteen-point fixed-set bound used to remove
the singleton orbits from the Mackey head estimate. -/
theorem four_le_card_fixedPoints [Finite X] [Finite I]
    (hP : IsPGroup 3 P) (hI : Nat.card I = 8) :
    4 ≤ Nat.card (MulAction.fixedPoints P X) := by
  have hpairs := two_le_card_fixedPairs F P hP hI
  have h := Nat.card_le_card_of_injective (fixedPointsEmbedding F P hP)
    (fixedPointsEmbedding F P hP).injective
  rw [Nat.card_prod, Nat.card_zmod] at h
  omega

end SymmetricSubgroupAsymptotics.BinaryPairTernaryFixedPoints

end
