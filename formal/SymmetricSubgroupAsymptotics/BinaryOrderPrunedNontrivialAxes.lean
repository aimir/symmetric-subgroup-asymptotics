import SymmetricSubgroupAsymptotics.BinaryOrderPrunedCoverage

/-! Nontrivial original normal axes save one binary order bit.

The quotient-cardinality argument holds for every finite group. Binary
structure is required explicitly only when the resulting order certificate
is used to bound surviving epimorphisms. The fixed selection leaves the
trivial axis unresolved; returning none is not a survival-exclusion proof.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryOrderPrunedNontrivialAxes

/-- A nontrivial literal normal has at least two elements, so its quotient
has at most half the original certified order. No p-group premise is used. -/
theorem quotient_card_le_of_ne_bot
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (a : ℕ) (hcard : Nat.card G ≤ 2^(a+1)) (hN : N ≠ ⊥) :
    Nat.card (G ⧸ N) ≤ 2^a := by
  have hNcard : 2 ≤ Nat.card N := N.one_lt_card_iff_ne_bot.mpr hN
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hquot : Nat.card (G ⧸ N) * 2 ≤ 2^a * 2 := by
    calc
      _ ≤ Nat.card (G ⧸ N) * Nat.card N := Nat.mul_le_mul_left _ hNcard
      _ = Nat.card G := hmul.symm
      _ ≤ _ := by simpa only [pow_succ] using hcard
  omega

/-- Install the existing order-gap certificate for the same original
normal subgroup and the same original physical width. -/
def certificateOfNontrivial {w a : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (N : Subgroup U) [N.Normal]
    (hcard : Nat.card U ≤ 2^(a+1)) (hN : N ≠ ⊥) (hgap : 2*a < w) :
    BinaryTargetOrderCertificate U N :=
  BinaryOrderPrunedCoverage.certificateOfQuotientCard U N
    (quotient_card_le_of_ne_bot N a hcard hN) hgap

theorem certificateOfNontrivial_prefixDegree_le {w a : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (N : Subgroup U) [N.Normal]
    (hcard : Nat.card U ≤ 2^(a+1)) (hN : N ≠ ⊥) (hgap : 2*a < w) :
    (certificateOfNontrivial U N hcard hN hgap).prefixDegree ≤ 2*a := by
  apply Nat.mul_le_mul_left 2
  simpa only [Nat.log_pow (by decide : 1 < 2)] using
    (Nat.log_mono_right (b := 2) (quotient_card_le_of_ne_bot N a hcard hN))

/-- Certificate choices depend only on the actual normal axis, before any
exterior degree, source J, predicate, or weight is chosen. -/
def selectionOfNontrivial {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (a : ℕ)
    (hcard : Nat.card U ≤ 2^(a+1)) (hgap : 2*a < w) :
    BinaryPairOrderSelection U := fun N =>
  if hN : N.1 = ⊥ then none
  else some (.inr (certificateOfNontrivial U N.1 hcard hN hgap))

/-- Exactly the trivial original normal remains to be handled separately.
This statement makes no assertion that its surviving maps vanish. -/
theorem selectionOfNontrivial_eq_none_iff {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (a : ℕ)
    (hcard : Nat.card U ≤ 2^(a+1)) (hgap : 2*a < w)
    (N : {N : Subgroup U // N.Normal}) :
    selectionOfNontrivial U a hcard hgap N = none ↔ N.1 = ⊥ := by
  by_cases hN : N.1 = ⊥ <;> simp [selectionOfNontrivial, hN]

theorem selectionOfNontrivial_prefixDegree {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (a : ℕ)
    (hcard : Nat.card U ≤ 2^(a+1)) (hgap : 2*a < w)
    (N : {N : Subgroup U // N.Normal}) (hN : N.1 ≠ ⊥) :
    (selectionOfNontrivial U a hcard hgap).prefixDegree N =
      2 * Nat.log 2 (Nat.card (U ⧸ N.1)) := by
  simp [selectionOfNontrivial, hN, BinaryPairOrderSelection.prefixDegree,
    BinaryPairOrderCertificate.prefixDegree, BinaryTargetOrderCertificate.prefixDegree]

theorem selectionOfNontrivial_liftConstant {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (a : ℕ)
    (hcard : Nat.card U ≤ 2^(a+1)) (hgap : 2*a < w)
    (N : {N : Subgroup U // N.Normal}) (hN : N.1 ≠ ⊥) :
    (selectionOfNontrivial U a hcard hgap).liftConstant N = 1 := by
  simp [selectionOfNontrivial, hN, BinaryPairOrderSelection.liftConstant,
    BinaryPairOrderCertificate.liftConstant, BinaryTargetOrderCertificate.liftConstant]

/-- The actual surviving-map bound uses an explicit binary hypothesis on
U. An arbitrary order inequality alone is never treated as that hypothesis. -/
theorem original_survivingEpiCount_le {w a b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (N : Subgroup U) [N.Normal]
    (hU : IsPGroup 2 U) (hcard : Nat.card U ≤ 2^(a+1))
    (hN : N ≠ ⊥) (hgap : 2*a < w)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P ⟨N, inferInstance⟩ J ≤
      (certificateOfNontrivial U N hcard hN hgap).momentWeight J :=
  (certificateOfNontrivial U N hcard hN hgap).original_survivingEpiCount_le hU P J

/-- At an actual even width the installed order branch has unit local
factor, retaining the same U, N, original survival predicate, and source J. -/
theorem original_survivingEpiCount_le_localFactor {h a b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin (2*h)))) (N : Subgroup U) [N.Normal]
    (hU : IsPGroup 2 U) (hcard : Nat.card U ≤ 2^(a+1))
    (hN : N ≠ ⊥) (hgap : 2*a < 2*h)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    let C := certificateOfNontrivial U N hcard hN hgap
    fusionSurvivingEpiCount U P ⟨N, inferInstance⟩ J ≤
      fusionLocalFactor b h C.prefixDegree C.liftConstant C.gapParameter * C.momentWeight J :=
  (certificateOfNontrivial U N hcard hN hgap).original_survivingEpiCount_le_localFactor hU P J

/-- Every nontrivial normal of an original degree-sixteen source of order
at most 256 has an actual quotient of order at most 128. -/
theorem sixteen_quotient_card_le
    (U : Subgroup (Equiv.Perm (Fin 16))) (N : Subgroup U) [N.Normal]
    (hcard : Nat.card U ≤ 256) (hN : N ≠ ⊥) :
    Nat.card (U ⧸ N) ≤ 128 :=
  quotient_card_le_of_ne_bot N 7 hcard hN

def sixteenCertificate
    (U : Subgroup (Equiv.Perm (Fin 16))) (N : Subgroup U) [N.Normal]
    (hcard : Nat.card U ≤ 256) (hN : N ≠ ⊥) : BinaryTargetOrderCertificate U N :=
  certificateOfNontrivial (a := 7) U N hcard hN (by decide : 2*7 < 16)

theorem sixteenCertificate_prefixDegree_le
    (U : Subgroup (Equiv.Perm (Fin 16))) (N : Subgroup U) [N.Normal]
    (hcard : Nat.card U ≤ 256) (hN : N ≠ ⊥) :
    (sixteenCertificate U N hcard hN).prefixDegree ≤ 14 :=
  certificateOfNontrivial_prefixDegree_le (a := 7) U N hcard hN (by decide : 2*7 < 16)

/-- A checked boundary source leaves only its trivial normal axis for
further pair/character work. All nontrivial axes are installed uniformly. -/
def sixteenSelection (U : Subgroup (Equiv.Perm (Fin 16)))
    (hcard : Nat.card U ≤ 256) : BinaryPairOrderSelection U :=
  selectionOfNontrivial U 7 hcard (by decide)

theorem sixteenSelection_eq_none_iff
    (U : Subgroup (Equiv.Perm (Fin 16))) (hcard : Nat.card U ≤ 256)
    (N : {N : Subgroup U // N.Normal}) :
    sixteenSelection U hcard N = none ↔ N.1 = ⊥ :=
  selectionOfNontrivial_eq_none_iff U 7 hcard (by decide) N

end SymmetricSubgroupAsymptotics.BinaryOrderPrunedNontrivialAxes
