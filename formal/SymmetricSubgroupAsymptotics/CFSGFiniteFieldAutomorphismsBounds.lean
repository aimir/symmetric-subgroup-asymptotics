import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Quantitative bounds for actual finite-field automorphisms. The
field factor has size at most log₂ of the original field cardinality;
for a pinned Galois-field presentation its size is exactly the original
extension exponent. No simple-group outer-automorphism identification
is assumed or asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms
variable (F : Type*) [Field F] [Finite F]

/-- Exact logarithmic field-size identity for the actual field factor. -/
theorem card_ringAut_mul_logb_characteristic (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] :
    (Nat.card (F ≃+* F) : ℝ)*Real.logb 2 p=Real.logb 2 (Nat.card F) := by
  have he : (Nat.card F : ℝ)=(p : ℝ)^Nat.card (F ≃+* F) := by
    exact_mod_cast (field_card_eq_pow_card_ringAut F p).symm
  rw [he,Real.logb_pow]

/-- The actual automorphism group is bounded by log₂ of field size,
independently of the choice of prime-field algebra presentation. -/
theorem card_ringAut_le_logb_of_primeField (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] :
    (Nat.card (F ≃+* F) : ℝ)≤Real.logb 2 (Nat.card F) := by
  have hn : 2^Nat.card (F ≃+* F)≤Nat.card F :=
    (Nat.pow_le_pow_left (Fact.out : p.Prime).two_le _).trans_eq
      (field_card_eq_pow_card_ringAut F p)
  have hr : (2 : ℝ)^Nat.card (F ≃+* F)≤(Nat.card F : ℝ) := by exact_mod_cast hn
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (by positivity : (0 : ℝ)<(2 : ℝ)^Nat.card (F ≃+* F)) hr
  simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] using hl

/-- Every finite field, with no supplied field presentation or extra
hypothesis, satisfies the exact field-factor bound used in Lie families. -/
theorem card_ringAut_le_logb :
    (Nat.card (F ≃+* F) : ℝ)≤Real.logb 2 (Nat.card F) := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨_,hp,_⟩ := FiniteField.card F (ringChar F)
  letI : Fact (ringChar F).Prime := ⟨hp⟩
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  exact card_ringAut_le_logb_of_primeField F (ringChar F)

/-- Exact cardinality for the same Galois-field types used in the pinned
CFSG field parameter, with their original extension exponent retained. -/
theorem card_galoisField_ringAut (p e : ℕ) [Fact p.Prime] (he : e≠0) :
    Nat.card (GaloisField p e ≃+* GaloisField p e)=e := by
  rw [card_ringAut (GaloisField p e) p,GaloisField.finrank p he]

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms
