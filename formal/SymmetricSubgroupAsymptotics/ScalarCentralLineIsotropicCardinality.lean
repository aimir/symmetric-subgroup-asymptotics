import SymmetricSubgroupAsymptotics.CFSGHeisenbergFiniteFieldIsotropy

/-! Isotropy with an enlarged actual central kernel. Its intersection
may be diagonal across a distinguished scalar line and all the other
central coordinates. Pulling that SAME intersection back to the actual
line preserves the prime-field annihilator argument; no quotient is
declared centre-proper and no full-field linearity is imposed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarCentralLineIsotropicCardinality

theorem proper_additive_card_mul_prime_le (p : ℕ) [Fact p.Prime]
    {Z : Type*} [AddCommGroup Z] [Module (ZMod p) Z] [Finite Z]
    (C : AddSubgroup Z) (hC : C ≠ ⊤) : p*Nat.card C ≤ Nat.card Z := by
  letI : Module.Finite (ZMod p) Z := Module.Finite.of_finite
  let L := AddSubgroup.toZModSubmodule p C
  have hL : L ≠ ⊤ := by
    intro he
    apply hC
    apply top_unique
    intro z _
    have hz : z ∈ L := by rw [he]; trivial
    exact hz
  have hd : Module.finrank (ZMod p) L < Module.finrank (ZMod p) Z :=
    Submodule.finrank_lt hL
  have hc : Nat.card C=p^Module.finrank (ZMod p) L := by
    change Nat.card L = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_zmod]
  have hz : Nat.card Z=p^Module.finrank (ZMod p) Z := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_zmod]
  calc
    p*Nat.card C=p^(Module.finrank (ZMod p) L+1) := by
      rw [hc,pow_succ,Nat.mul_comm]
    _ ≤ p^Module.finrank (ZMod p) Z :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    _ = Nat.card Z := hz.symm

theorem card_le_of_scalar_line_pairing
    {F V Z : Type*} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] [Finite V] [AddCommGroup Z]
    (p m : ℕ) [Fact p.Prime] [CharP F p]
    (B : V →ₗ[F] V →ₗ[F] F) (hAlt : ∀ v, B v v=0)
    (hfull : ∀ v, v≠0 → Function.Surjective (B v))
    (hdim : Module.finrank F V=2*m)
    (ι : F →+ Z) (C : AddSubgroup Z) (hline : ι 1 ∉ C)
    (W : AddSubgroup V) (hW : ∀ v∈W, ∀ w∈W, ι (B v w) ∈ C) :
    Nat.card W ≤ Nat.card F^m := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Module (ZMod p) V := Module.restrictScalars (ZMod p) F V
  letI : IsScalarTower (ZMod p) F V := IsScalarTower.restrictScalars (ZMod p) F V
  letI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let Cline := C.comap ι
  have hCline : Cline ≠ ⊤ := by
    intro he
    apply hline
    have h : (1 : F)∈Cline := by rw [he]; trivial
    exact h
  let Bp := B.restrictScalars₁₂ (ZMod p) (ZMod p)
  let L := AddSubgroup.toZModSubmodule p W
  have hd : 2*Module.finrank (ZMod p) L ≤ Module.finrank (ZMod p) V :=
    CFSGHeisenbergCentralIsotropy.additive_twice_finrank_le p Bp
      hAlt hfull Cline hCline W hW
  have hw : Nat.card W=p^Module.finrank (ZMod p) L := by
    change Nat.card L = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_zmod]
  have hv : Nat.card V=p^Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_zmod]
  have hs : Nat.card W^2 ≤ Nat.card V := by
    rw [hw,hv,←pow_mul]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      (by simpa only [Nat.mul_comm] using hd)
  have hc : Nat.card V=(Nat.card F^m)^2 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := V),hdim,←pow_mul]
    congr 1
    omega
  rw [hc] at hs
  exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp hs

end SymmetricSubgroupAsymptotics.ScalarCentralLineIsotropicCardinality
