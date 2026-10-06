import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain

/-!
# Central prime socle factors from original relative heads

The fixed-frame calculation bounds the relative prime head of every normal
subgroup of the original extension.  This file turns that bound into the
normal-generator bound for the central prime-primary part of the socle of
every original quotient.

The argument is quotient-natural.  Given `N ◁ G`, pull the central
prime-primary socle part of `G/N` back to an original normal subgroup `K`.
The normal-chain rank identity shows that the relative head of `K/N` is no
larger than the original relative head of `K`.  Centrality identifies the
relative characters of `K/N` with all of its prime characters, and
Burnside's basis theorem then supplies the normal generators.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G : Type} [Group G] [Finite G]

/-- When the ambient conjugation action is trivial, relative characters
are the complete prime-character space. -/
def primeRelativeCharactersEquivPrimeCharactersOfCentral
    (H : Subgroup G) [H.Normal]
    (hcentral : H ≤ Subgroup.center G) :
    primeRelativeCharacters p H ≃ₗ[ZMod p] PrimeCharacters p H where
  toFun χ := χ.1
  invFun χ := ⟨χ, by
    intro g h
    have hc : g * (h : G) = (h : G) * g :=
      Subgroup.mem_center_iff.mp (hcentral h.2) g
    have hconj :
        (⟨g * (h : G) * g⁻¹,
          Subgroup.Normal.conj_mem inferInstance (h : G) h.2 g⟩ : H) = h := by
      apply Subtype.ext
      calc
        g * (h : G) * g⁻¹ = (h : G) * g * g⁻¹ :=
          congrArg (fun x : G ↦ x * g⁻¹) hc
        _ = (h : G) := by simp only [mul_assoc, mul_inv_cancel, mul_one]
    exact congrArg (fun x : H ↦ χ (Additive.ofMul x)) hconj⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A quotient term in a normal chain cannot have larger relative head
than the original upper subgroup.  This is the monotone consequence of
the exact retained-annihilator identity. -/
theorem primeRelativeHead_normalChainQuotient_le
    (B C : Subgroup G) [B.Normal] [C.Normal] (hBC : B ≤ C) :
    Module.finrank (ZMod p)
        (primeRelativeCharacters p (normalChainQuotient B C)) ≤
      Module.finrank (ZMod p) (primeRelativeCharacters p C) := by
  rw [primeRelativeHead_chain_eq B C p hBC]
  exact Nat.le_add_right _ _

/-- A central prime-group normal section is generated within the ambient
group by no more elements than the original relative head of its preimage.
The conclusion concerns the literal normal-chain quotient, so it can be
rewritten to any concrete quotient subgroup only after its actual pullback
has been fixed. -/
theorem normalGen_centralPrime_normalChainQuotient_le_relativeHead
    (B C : Subgroup G) [B.Normal] [C.Normal] (hBC : B ≤ C)
    (hp : IsPGroup p (normalChainQuotient B C))
    (hcentral : normalChainQuotient B C ≤
      Subgroup.center (G ⧸ B)) :
    MarkedC4.normalGen (normalChainQuotient B C) ≤
      Module.finrank (ZMod p) (primeRelativeCharacters p C) := by
  calc
    MarkedC4.normalGen (normalChainQuotient B C) ≤
        Module.finrank (ZMod p)
          (PrimeCharacters p (normalChainQuotient B C)) :=
      MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank
        p (normalChainQuotient B C) hp
    _ = Module.finrank (ZMod p)
          (primeRelativeCharacters p (normalChainQuotient B C)) :=
      (primeRelativeCharactersEquivPrimeCharactersOfCentral
        p (normalChainQuotient B C) hcentral).finrank_eq.symm
    _ ≤ Module.finrank (ZMod p) (primeRelativeCharacters p C) :=
      primeRelativeHead_normalChainQuotient_le p B C hBC

/-- The central `p`-primary part of the ambient socle.  The predicate is
intrinsic to the literal quotient group and therefore includes all central
minimal normal factors of characteristic `p`, without choosing abstract
simple-type labels. -/
abbrev centralPrimeSoclePart (p : ℕ) (G : Type)
    [Group G] [Finite G] : Subgroup G :=
  minimalNormalSoclePart G
    (fun M ↦ M ≤ Subgroup.center G ∧ IsPGroup p M)

instance centralPrimeSoclePart_normal :
    (centralPrimeSoclePart p G).Normal := by
  dsimp only [centralPrimeSoclePart]
  infer_instance

omit [Fact p.Prime] in
theorem centralPrimeSoclePart_le_center :
    centralPrimeSoclePart p G ≤ Subgroup.center G := by
  apply minimalNormalSoclePart_le_of
  intro M _ hM
  exact hM.1

theorem centralPrimeSoclePart_isPGroup :
    IsPGroup p (centralPrimeSoclePart p G) := by
  simpa only [centralPrimeSoclePart] using
    primePrimarySoclePart_isPGroup_of_predicate p G
      (fun M ↦ M ≤ Subgroup.center G)

/-- Uniform original-axis form used by fixed-frame arguments.  A relative
head bound on every original normal subgroup controls the central
prime-primary socle of every literal quotient, with no splitting or
classification of the extension. -/
theorem centralPrimeSoclePart_normalGen_le_of_allRelativeHeads
    (slots : ℕ)
    (hhead : ∀ K : {K : Subgroup G // K.Normal},
      Module.finrank (ZMod p) (primeRelativeCharacters p K.1) ≤ slots)
    (N : {N : Subgroup G // N.Normal}) :
    MarkedC4.normalGen (centralPrimeSoclePart p (G ⧸ N.1)) ≤ slots := by
  let q : G →* G ⧸ N.1 := QuotientGroup.mk' N.1
  let A : Subgroup (G ⧸ N.1) := centralPrimeSoclePart p (G ⧸ N.1)
  let K : Subgroup G := A.comap q
  letI : N.1.Normal := N.2
  letI : A.Normal := by
    dsimp only [A]
    infer_instance
  letI : K.Normal := Subgroup.Normal.comap inferInstance q
  have hNK : N.1 ≤ K := by
    intro n hn
    change q n ∈ A
    rw [show q n = 1 by
      exact (QuotientGroup.eq_one_iff (N := N.1) n).mpr hn]
    exact A.one_mem
  have hquot : normalChainQuotient N.1 K = A := by
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N.1) A
  have hp : IsPGroup p (normalChainQuotient N.1 K) := by
    rw [hquot]
    exact centralPrimeSoclePart_isPGroup p (G := G ⧸ N.1)
  have hcentral : normalChainQuotient N.1 K ≤
      Subgroup.center (G ⧸ N.1) := by
    rw [hquot]
    exact centralPrimeSoclePart_le_center p (G := G ⧸ N.1)
  have h := normalGen_centralPrime_normalChainQuotient_le_relativeHead
    p N.1 K hNK hp hcentral
  rw [hquot] at h
  exact h.trans (hhead ⟨K, inferInstance⟩)

end SymmetricSubgroupAsymptotics

end
