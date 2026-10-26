import SymmetricSubgroupAsymptotics.FrattiniAffineQuotient
import SymmetricSubgroupAsymptotics.PrimeFrattiniCardinality
import SymmetricSubgroupAsymptotics.ElementaryPrimeHolomorphClassBound

/-! Every subgroup of the original finite p-group affine envelope is
mapped into the SAME genuine elementary affine image. Frattini fibres
and the actual prime rank jointly pay the retained kernel factor. This
does not require the original translation group to be abelian. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FrattiniAffineSmallClassBound
open ElementaryPrimeHolomorphClassBound

variable (p : ℕ) [Fact p.Prime] (N : Type) [Group N] [Finite N]
    {C : Type} [Group C] [Finite C] (φ : C →* MulAut N)

private theorem quotient_card : Nat.card (Multiplicative (PrimeAbelianization p N))=
    p^Module.finrank (ZMod p) (PrimeCharacters p N) := by
  change Nat.card (PrimeAbelianization p N)=_
  rw [Module.natCard_eq_pow_finrank (K:=ZMod p),Nat.card_zmod,Subspace.dual_finrank_eq]

theorem binary_rank_bound (hp : p=2) (hN : IsPGroup p N)
    (hφ : Function.Injective φ) (d : ℕ) (hd : d≤6) (hcard : Nat.card N=p^d)
    (H : Subgroup (N ⋊[φ] C)) :
    Nat.card (ConjClasses H)≤
      p^((d-Module.finrank (ZMod p) (PrimeCharacters p N))*
        (Module.finrank (ZMod p) (PrimeCharacters p N)+1))*
          binaryBudget (Module.finrank (ZMod p) (PrimeCharacters p N)) := by
  subst p
  let W := PrimeAbelianization 2 N
  let eA : Additive (Multiplicative W)≃+W := AddEquiv.additiveMultiplicative W
  letI : Module (ZMod 2) (Additive (Multiplicative W)) := eA.module (ZMod 2)
  let R := ((FrattiniAffineQuotient.quotientHom 2 N φ).comp H.subtype).range
  have hR : Nat.card (ConjClasses R)≤
      binaryBudget (Module.finrank (ZMod 2) (PrimeCharacters 2 N)) :=
    binary_subgroup_class_card_le (Module.finrank (ZMod 2) (PrimeCharacters 2 N))
      ((PrimeFrattiniCardinality.rank_le_exponent 2 N d hcard).trans hd)
      (quotient_card 2 N) R
  have hb := (FrattiniAffineQuotient.subgroup_class_card_le 2 N φ hN hφ H).trans
    (Nat.mul_le_mul_left _ hR)
  simpa only [PrimeFrattiniCardinality.frattini_card 2 N hN d hcard,← pow_mul] using hb

theorem ternary_rank_bound (hp : p=3) (hN : IsPGroup p N)
    (hφ : Function.Injective φ) (d : ℕ) (hd : d≤3) (hcard : Nat.card N=p^d)
    (H : Subgroup (N ⋊[φ] C)) :
    Nat.card (ConjClasses H)≤
      p^((d-Module.finrank (ZMod p) (PrimeCharacters p N))*
        (Module.finrank (ZMod p) (PrimeCharacters p N)+1))*
          ternaryBudget (Module.finrank (ZMod p) (PrimeCharacters p N)) := by
  subst p
  let W := PrimeAbelianization 3 N
  let eA : Additive (Multiplicative W)≃+W := AddEquiv.additiveMultiplicative W
  letI : Module (ZMod 3) (Additive (Multiplicative W)) := eA.module (ZMod 3)
  let R := ((FrattiniAffineQuotient.quotientHom 3 N φ).comp H.subtype).range
  have hR : Nat.card (ConjClasses R)≤
      ternaryBudget (Module.finrank (ZMod 3) (PrimeCharacters 3 N)) :=
    ternary_subgroup_class_card_le (Module.finrank (ZMod 3) (PrimeCharacters 3 N))
      ((PrimeFrattiniCardinality.rank_le_exponent 3 N d hcard).trans hd)
      (quotient_card 3 N) R
  have hb := (FrattiniAffineQuotient.subgroup_class_card_le 3 N φ hN hφ H).trans
    (Nat.mul_le_mul_left _ hR)
  simpa only [PrimeFrattiniCardinality.frattini_card 3 N hN d hcard,← pow_mul] using hb

def binaryClassBudget (d : ℕ) : ℕ :=
  if d=3 then 40 else if d=4 then 772 else if d=5 then 351240 else 32*(2^30+1)

theorem binary_scalar_capacity (d r : ℕ) (hd3 : 3≤d) (hd6 : d≤6) (hr : r≤d) :
    (2:ℕ)^((d-r)*(r+1))*binaryBudget r≤binaryClassBudget d := by
  interval_cases d <;> interval_cases r <;>
    norm_num [binaryBudget,binaryClassBudget]

theorem ternary_scalar_capacity (r : ℕ) (hr : r≤3) :
    (3:ℕ)^((3-r)*(r+1))*ternaryBudget r≤12247 := by
  interval_cases r <;> norm_num [ternaryBudget]

theorem binary_subgroup_class_card_le (hp : p=2) (hN : IsPGroup p N)
    (hφ : Function.Injective φ) (d : ℕ) (hd3 : 3≤d) (hd6 : d≤6)
    (hcard : Nat.card N=p^d) (H : Subgroup (N ⋊[φ] C)) :
    Nat.card (ConjClasses H)≤binaryClassBudget d := by
  subst p
  exact (binary_rank_bound 2 N φ rfl hN hφ d hd6 hcard H).trans
    (binary_scalar_capacity d (Module.finrank (ZMod 2) (PrimeCharacters 2 N)) hd3 hd6
      (PrimeFrattiniCardinality.rank_le_exponent 2 N d hcard))

theorem ternary_subgroup_class_card_le (hp : p=3) (hN : IsPGroup p N)
    (hφ : Function.Injective φ) (hcard : Nat.card N=p^3)
    (H : Subgroup (N ⋊[φ] C)) : Nat.card (ConjClasses H)≤12247 := by
  subst p
  exact (ternary_rank_bound 3 N φ rfl hN hφ 3 (by decide) hcard H).trans
    (ternary_scalar_capacity (Module.finrank (ZMod 3) (PrimeCharacters 3 N))
      (PrimeFrattiniCardinality.rank_le_exponent 3 N 3 hcard))

end SymmetricSubgroupAsymptotics.FrattiniAffineSmallClassBound
