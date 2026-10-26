import SymmetricSubgroupAsymptotics.PrimeFrattiniGenerators

/-! Exact cardinal arithmetic of the original Frattini quotient. The
rank and Frattini order share the SAME original p-power order; no
commutativity or primitive action of the source group is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeFrattiniCardinality

variable (p : ℕ) [Fact p.Prime] (N : Type*) [Group N] [Finite N]

theorem quotient_card (hN : IsPGroup p N) :
    Nat.card (N ⧸ frattini N)=
      p^Module.finrank (ZMod p) (PrimeCharacters p N) := by
  simpa only [Subspace.dual_finrank_eq] using primeFrattini_quotient_card p N hN

theorem rank_le_exponent (d : ℕ) (hcard : Nat.card N=p^d) :
    Module.finrank (ZMod p) (PrimeCharacters p N)≤d := by
  apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
  exact (primeCharacters_pow_finrank_le_card p N).trans_eq hcard

theorem frattini_card (hN : IsPGroup p N) (d : ℕ) (hcard : Nat.card N=p^d) :
    Nat.card (frattini N)=
      p^(d-Module.finrank (ZMod p) (PrimeCharacters p N)) := by
  have hr := rank_le_exponent p N d hcard
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos
    (Module.finrank (ZMod p) (PrimeCharacters p N)))
  calc
    Nat.card (frattini N)*p^Module.finrank (ZMod p) (PrimeCharacters p N)=
        Nat.card (frattini N)*Nat.card (N ⧸ frattini N) := by
      rw [quotient_card p N hN]
    _=Nat.card N := by
      rw [← (frattini N).index_eq_card]
      exact (frattini N).card_mul_index
    _=p^d := hcard
    _=p^(d-Module.finrank (ZMod p) (PrimeCharacters p N))*
        p^Module.finrank (ZMod p) (PrimeCharacters p N) := by
      rw [← pow_add,Nat.sub_add_cancel hr]

end SymmetricSubgroupAsymptotics.PrimeFrattiniCardinality
