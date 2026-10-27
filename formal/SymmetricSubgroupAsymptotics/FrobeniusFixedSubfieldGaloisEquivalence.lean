import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The actual Frobenius-fixed subfield of an algebraically closed field
has p^e elements and is isomorphic to the literal GaloisField p e.  The
input membership equation is the defining equation of that subfield,
not a supplied cardinality or a named-model identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FrobeniusFixedSubfieldGaloisEquivalence
open Polynomial

variable {L : Type*} [Field L] [IsAlgClosed L]
variable (p e : ℕ) [Fact p.Prime] [CharP L p]

theorem card_eq (he : 0 < e) (K : Subfield L)
    (hK : ∀ x : L, x ∈ K ↔ x^(p^e)=x) : Nat.card K = p^e := by
  let P : L[X] := X^(p^e)-X
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hP : P ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero L (Nat.ne_of_gt he) hp
  have hset : (K : Set L)=P.rootSet L := by
    ext x
    change x ∈ K ↔ x ∈ P.rootSet L
    rw [hK,mem_rootSet_of_ne hP]
    simp only [P,map_sub,aeval_X_pow,aeval_X,sub_eq_zero]
  have hsep : P.Separable :=
    galois_poly_separable p (p^e) (dvd_pow (dvd_refl p) (Nat.ne_of_gt he))
  have hsplit : (P.map (algebraMap L L)).Splits := by
    simpa only [Algebra.algebraMap_self,Polynomial.map_id] using (IsAlgClosed.splits P)
  calc
    Nat.card K = Nat.card (P.rootSet L) := Nat.card_congr (Equiv.setCongr hset)
    _ = Fintype.card (P.rootSet L) := Nat.card_eq_fintype_card
    _ = P.natDegree := card_rootSet_eq_natDegree hsep hsplit
    _ = p^e := FiniteField.X_pow_card_pow_sub_X_natDegree_eq L (Nat.ne_of_gt he) hp

def fieldEquiv (he : 0 < e) (K : Subfield L)
    (hK : ∀ x : L, x ∈ K ↔ x^(p^e)=x) : K ≃+* GaloisField p e := by
  have hc := card_eq p e he K hK
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  exact (GaloisField.algEquivGaloisField (p := p) (n := e) hc).toRingEquiv

end SymmetricSubgroupAsymptotics.FrobeniusFixedSubfieldGaloisEquivalence
