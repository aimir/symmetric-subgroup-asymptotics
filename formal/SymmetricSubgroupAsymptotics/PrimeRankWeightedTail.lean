import SymmetricSubgroupAsymptotics.JointSourceGraphs
import SymmetricSubgroupAsymptotics.PrimeElementaryEpimorphismBound

/-!
# Same-source weighted tails for every prime character rank

The binary rank-tail argument is not intrinsically binary.  For a prime
`p`, `a` independent `ZMod p` characters have a faithful marker action on
`p * a` points, obtained by putting the regular cyclic action in each of
`a` disjoint columns.  The shared-source graph injection therefore gives

`sum_J p^(q * a * d_p(J)) <= s_(b + q * p * a)`.

The final two theorems are the corresponding full and hot weighted sums for
one character per column.  They are stated over the literal subgroup source
`J <= S_b`, so they can be used by the affine retained-cell argument without
introducing an abstract replacement source.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

/-- `a` independent prime characters acting by translations in `a` disjoint
regular `p`-point columns. -/
def primeMarkerAction (a : ℕ) :
    Multiplicative (Fin a → ZMod p) →* Equiv.Perm (Fin a × ZMod p) where
  toFun x :=
    { toFun := fun y => (y.1, y.2 + x.toAdd y.1)
      invFun := fun y => (y.1, y.2 - x.toAdd y.1)
      left_inv := by intro y; simp
      right_inv := by intro y; simp }
  map_one' := by ext y <;> simp
  map_mul' x y := by ext z <;> simp [add_comm, add_left_comm]

theorem primeMarkerAction_injective (a : ℕ) :
    Function.Injective (primeMarkerAction p a) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  funext i
  have hi := congrArg Prod.snd (Equiv.congr_fun h (i, 0))
  simpa [primeMarkerAction] using hi

/-- Relabel the prime marker on the finite ordinal of its exact degree. -/
def primeMarkerFiniteAction (a : ℕ) :
    Multiplicative (Fin a → ZMod p) →* Equiv.Perm (Fin (p * a)) :=
  (Fintype.equivOfCardEq (by simp [Nat.mul_comm]) :
    (Fin a × ZMod p) ≃ Fin (p * a)).permCongrHom.toMonoidHom.comp
      (primeMarkerAction p a)

theorem primeMarkerFiniteAction_injective (a : ℕ) :
    Function.Injective (primeMarkerFiniteAction p a) :=
  (Fintype.equivOfCardEq (by simp [Nat.mul_comm]) :
    (Fin a × ZMod p) ≃ Fin (p * a)).permCongrHom.injective.comp
      (primeMarkerAction_injective p a)

/-- The complete same-source marker moment for `a` independent
`ZMod p` characters. -/
theorem primeCharacterRank_marker_moment_le (a b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        (p ^ (a * Module.finrank (ZMod p) (PrimeCharacters p J))) ^ q) ≤
      subgroupCount (b + q * (p * a)) := by
  have h := jointSourceHom_moment_le (primeMarkerFiniteAction p a)
    (primeMarkerFiniteAction_injective p a)
    (MonoidHom.id (Multiplicative (Fin a → ZMod p)))
    Function.surjective_id b q
  simpa only [primeAbelianizationGroupHom_card p, Module.finrank_pi,
    Fintype.card_fin, Nat.mul_comm] using h

/-- A complete quotient map and `a` prime-character columns are repeated on
the same source.  This is the mixed moment needed when an affine fixed row is
coupled to its literal quotient top. -/
theorem jointSourceEpimorphism_primeRank_moment_le
    {A B : Type*} [Group A] [Group B] [Finite B] {s : ℕ}
    (rho : A →* Equiv.Perm (Fin s)) (hrho : Function.Injective rho)
    (pi : A →* B) (hpi : Function.Surjective pi)
    (b a q : ℕ) :
    ∑ J : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card (GroupEpimorphism J B) *
          p ^ (a * Module.finrank (ZMod p) (PrimeCharacters p J))) ^ q ≤
      subgroupCount (b + q * (s + p * a)) := by
  have h := jointSourceMarked_moment_le rho hrho
    (primeMarkerFiniteAction p a) (primeMarkerFiniteAction_injective p a)
    pi hpi b q
  simpa only [primeAbelianizationGroupHom_card p, Module.finrank_pi,
    Fintype.card_fin, Nat.mul_comm] using h

/-- Real-valued full weighted sum for one prime character per marker
column. -/
theorem primeRankWeightedFullSum_le (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        (p : ℝ) ^ ((q : ℝ) *
          Module.finrank (ZMod p) (PrimeCharacters p J))) ≤
      (subgroupCount (b + p * q) : ℝ) := by
  have h := primeCharacterRank_marker_moment_le p 1 b q
  have hsum :
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
          (p : ℝ) ^ ((q : ℝ) *
            Module.finrank (ZMod p) (PrimeCharacters p J))) =
        ((∑ J : Subgroup (Equiv.Perm (Fin b)),
          (p ^ (1 * Module.finrank (ZMod p) (PrimeCharacters p J))) ^ q : ℕ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [one_mul, ← pow_mul, mul_comm, ← Real.rpow_natCast]
    push_cast
    ring_nf
  rw [hsum, show b + p * q = b + q * (p * 1) by ring]
  exact_mod_cast h

/-- Tilted hot tail for the prime character rank.  On the locus
`a*b < d_p(J)`, any residual weight `p^(ell*d_p(J))` with `ell <= q` is
absorbed by the `q`-th same-source marker moment. -/
theorem primeRankWeightedHotSum_le
    (a : ℝ) (b q ell : ℕ) (hell : ell ≤ q) :
    (p : ℝ) ^ (((q : ℝ) - ell) * a * b) *
        (∑ J ∈ Finset.univ.filter
            (fun J : Subgroup (Equiv.Perm (Fin b)) =>
              a * b < Module.finrank (ZMod p) (PrimeCharacters p J)),
          (p : ℝ) ^ ((ell : ℝ) *
            Module.finrank (ZMod p) (PrimeCharacters p J))) ≤
      (subgroupCount (b + p * q) : ℝ) := by
  refine le_trans ?_ (primeRankWeightedFullSum_le p b q)
  rw [Finset.mul_sum]
  calc
    (∑ J ∈ Finset.univ.filter
          (fun J : Subgroup (Equiv.Perm (Fin b)) =>
            a * b < Module.finrank (ZMod p) (PrimeCharacters p J)),
        (p : ℝ) ^ (((q : ℝ) - ell) * a * b) *
          (p : ℝ) ^ ((ell : ℝ) *
            Module.finrank (ZMod p) (PrimeCharacters p J))) ≤
      ∑ J ∈ Finset.univ.filter
          (fun J : Subgroup (Equiv.Perm (Fin b)) =>
            a * b < Module.finrank (ZMod p) (PrimeCharacters p J)),
        (p : ℝ) ^ ((q : ℝ) *
          Module.finrank (ZMod p) (PrimeCharacters p J)) := by
      apply Finset.sum_le_sum
      intro J hJ
      have hhot : a * b <
          Module.finrank (ZMod p) (PrimeCharacters p J) :=
        (Finset.mem_filter.mp hJ).2
      have hqell : (0 : ℝ) ≤ (q : ℝ) - ell := by
        have : (ell : ℝ) ≤ q := by exact_mod_cast hell
        linarith
      rw [← Real.rpow_add (by exact_mod_cast (Fact.out : p.Prime).pos)]
      apply Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
      have hmul := mul_le_mul_of_nonneg_left hhot.le hqell
      nlinarith
    _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),
        (p : ℝ) ^ ((q : ℝ) *
          Module.finrank (ZMod p) (PrimeCharacters p J)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)

end SymmetricSubgroupAsymptotics

end
