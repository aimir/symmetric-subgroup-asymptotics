import Mathlib.FieldTheory.Finite.GaloisField

/-! The actual automorphism group of a finite field. Every ring
automorphism fixes its prime field, so it is an actual power of the
arithmetic Frobenius, with exact order and cardinality equal to the
prime-field extension degree. This file makes no assertion identifying
field automorphisms with outer automorphisms of a simple group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms
variable (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]

/-- Every literal field automorphism fixes the canonical prime field. -/
def primeFieldAutEquiv : (F ≃+* F) ≃* (F ≃ₐ[ZMod p] F) where
  toFun σ := AlgEquiv.ofRingEquiv (f:=σ) (fun x =>
    RingHom.congr_fun (RingHom.ext_zmod
      (σ.toRingHom.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) x)
  invFun σ := σ.toRingEquiv
  left_inv σ := by ext x;rfl
  right_inv σ := by ext x;rfl
  map_mul' σ τ := by ext x;rfl

@[simp] theorem primeFieldAutEquiv_apply (σ : F ≃+* F) (x : F) :
    primeFieldAutEquiv F p σ x=σ x := rfl

variable [Finite F]

/-- The original arithmetic Frobenius on the original finite field. -/
def primeFrobenius : F ≃+* F :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F).toRingEquiv

@[simp] theorem primeFrobenius_apply (x : F) : primeFrobenius F p x=x^p := by
  change FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F x=x^p
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic,ZMod.card]

/-- An exact finite enumeration by powers, with no abstract cyclic-group
identification replacing the actual automorphisms. -/
theorem bijective_primeFrobenius_pow :
    Function.Bijective (fun k : Fin (Module.finrank (ZMod p) F) =>
      primeFrobenius F p^k.val) := by
  have he : ∀ k : ℕ,(primeFieldAutEquiv F p).symm
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F^k)=primeFrobenius F p^k := by
    intro k
    rw [map_pow]
    rfl
  have hb := (primeFieldAutEquiv F p).symm.bijective.comp
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F)
  simpa only [Function.comp_def,he] using hb

theorem exists_primeFrobenius_pow (σ : F ≃+* F) :
    ∃ k : Fin (Module.finrank (ZMod p) F),primeFrobenius F p^k.val=σ :=
  (bijective_primeFrobenius_pow F p).2 σ

theorem mem_zpowers_primeFrobenius (σ : F ≃+* F) :
    σ∈Subgroup.zpowers (primeFrobenius F p) := by
  obtain ⟨k,hk⟩ := exists_primeFrobenius_pow F p σ
  exact Subgroup.mem_zpowers_iff.mpr ⟨(k.val : ℤ),by rw [zpow_natCast];exact hk⟩

theorem primeFrobenius_order :
    orderOf (primeFrobenius F p)=Module.finrank (ZMod p) F := by
  have he : (primeFieldAutEquiv F p).symm
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F)=primeFrobenius F p := rfl
  rw [←he,(primeFieldAutEquiv F p).symm.orderOf_eq]
  exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) F

/-- Exact order of the actual ring-automorphism group. -/
theorem card_ringAut : Nat.card (F ≃+* F)=Module.finrank (ZMod p) F := by
  have hc := Nat.card_congr (Equiv.ofBijective
    (fun k : Fin (Module.finrank (ZMod p) F) => primeFrobenius F p^k.val)
    (bijective_primeFrobenius_pow F p))
  simpa only [Nat.card_fin] using hc.symm

/-- The cardinality of the original field is the characteristic to the
exact cardinality of its actual automorphism group. -/
theorem field_card_eq_pow_card_ringAut : p^Nat.card (F ≃+* F)=Nat.card F := by
  rw [card_ringAut F p]
  exact FiniteField.pow_finrank_eq_natCard p F

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms
