import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergPrime

/-! The centre-valued pairing is the commutator in the SAME literal
fixed radical. An arbitrary subgroup missing the whole centre therefore
has a vector image of at most half the prime-field dimension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGSerreOrdinaryTwists CFSGTwistedANaturalMatrices
open CFSGTwistedAUnitaryParameters CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedAUnitaryUpperArrays

theorem fixedRadical_block_shape (q : CFSG.PrimePower) (s : ℕ) (g : fixedRadical q s) :
    ∃ b : q.Extension 2, blockFixedMatrixHom q s g.val =
      upperUnit (firstRow q s (fixedRadicalParameterHom q s g).toAdd)
        (fixedRadicalParameterHom q s g).toAdd b := by
  obtain ⟨w, v, b, hg⟩ := g.property
  have hs := blockFixedMatrixHom_isometry q s g.val
  rw [hg] at hs
  have hw : w = firstRow q s v := by
    funext i
    have hi := upperArray_isometry_left_entry (definingFieldAutomorphism q 2).toRingHom
      (parity q s) (middleForm q s) w v b hs i
    have hj := radicalRow_left (definingFieldAutomorphism q 2)
      (fun a => extension_two_pow_twice q a) (parity q s)
      (neg_one_pow_eq_or (q.Extension 2) s) (middleForm q s)
      (middleForm_hermitian q s) v i
    apply (definingFieldAutomorphism q 2).injective
    exact (eq_neg_of_add_eq_zero_left hi).trans (eq_neg_of_add_eq_zero_left hj).symm
  have hv : (fixedRadicalParameterHom q s g).toAdd = v := by
    change (fun i => (blockFixedMatrixHom q s g.val :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2))
        (.inr (.inl i)) (.inr (.inr ()))) = v
    rw [hg]
    rfl
  refine ⟨b, ?_⟩
  rw [hv, hg, hw]

theorem upperUnit_centralPair_commutator (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin (s + 1) → q.Extension 2) (b d : q.Extension 2) :
    ⁅upperUnit (firstRow q s v) v b, upperUnit (firstRow q s w) w d⁆ =
      upperUnit 0 0 (centralPairParameter q s v w) := by
  rw [upperUnit_commutator, ← centralPairParameter_eq_commutator]

def radicalPairElement (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin (s + 1) → q.Extension 2) : fixedRadical q s :=
  centralRadicalHom q s (Multiplicative.ofAdd (centralPair q s v w))

theorem fixedRadical_commutator (q : CFSG.PrimePower) (s : ℕ) (x y : fixedRadical q s) :
    ⁅x, y⁆ = radicalPairElement q s (fixedRadicalParameterHom q s x).toAdd
      (fixedRadicalParameterHom q s y).toAdd := by
  obtain ⟨b, hb⟩ := fixedRadical_block_shape q s x
  obtain ⟨d, hd⟩ := fixedRadical_block_shape q s y
  apply Subtype.ext
  apply blockFixedMatrixHom_injective q s
  change blockFixedMatrixHom q s ⁅x.val, y.val⁆ = blockFixedMatrixHom q s
    (centralRadicalElement q s (centralPair q s (fixedRadicalParameterHom q s x).toAdd
      (fixedRadicalParameterHom q s y).toAdd)).val
  rw [map_commutatorElement, hb, hd, upperUnit_centralPair_commutator,
    centralRadicalElement_block]
  rfl

def primeCentralRadicalHom (q : CFSG.PrimePower) (s : ℕ) :
    Multiplicative (primeCentralSpace q s) →* fixedRadical q s :=
  (centralRadicalHom q s).comp
    (AddMonoidHom.toMultiplicative (primeCentralEquiv q s).toAddMonoidHom)

def radicalVectorImage (q : CFSG.PrimePower) (s : ℕ) (H : Subgroup (fixedRadical q s)) :
    AddSubgroup (Fin (s + 1) → q.Extension 2) :=
  (H.map (fixedRadicalParameterHom q s)).toAddSubgroup'

def radicalCentralIntersection (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (fixedRadical q s)) : AddSubgroup (primeCentralSpace q s) :=
  (H.comap (primeCentralRadicalHom q s)).toAddSubgroup'

theorem radicalCentralIntersection_ne_top (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (fixedRadical q s)) (hH : ¬ (centralRadicalHom q s).range ≤ H) :
    radicalCentralIntersection q s H ≠ ⊤ := by
  intro he
  apply hH
  rintro g ⟨c, rfl⟩
  have hc : (primeCentralEquiv q s).symm c.toAdd ∈ radicalCentralIntersection q s H := by
    rw [he]
    trivial
  change centralRadicalHom q s (Multiplicative.ofAdd
    (primeCentralEquiv q s ((primeCentralEquiv q s).symm c.toAdd))) ∈ H at hc
  simpa only [AddEquiv.apply_symm_apply, ofAdd_toAdd] using hc

theorem radicalVectorImage_pairing_mem (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (fixedRadical q s))
    (v : Fin (s + 1) → q.Extension 2) (hv : v ∈ radicalVectorImage q s H)
    (w : Fin (s + 1) → q.Extension 2) (hw : w ∈ radicalVectorImage q s H) :
    primeCentralPairing q s v w ∈ radicalCentralIntersection q s H := by
  change Multiplicative.ofAdd v ∈ H.map (fixedRadicalParameterHom q s) at hv
  change Multiplicative.ofAdd w ∈ H.map (fixedRadicalParameterHom q s) at hw
  obtain ⟨x, hx, hpx⟩ := hv
  obtain ⟨y, hy, hpy⟩ := hw
  have hpx' : (fixedRadicalParameterHom q s x).toAdd = v :=
    congrArg Multiplicative.toAdd hpx
  have hpy' : (fixedRadicalParameterHom q s y).toAdd = w :=
    congrArg Multiplicative.toAdd hpy
  have hxy := fixedRadical_commutator q s x y
  rw [hpx', hpy'] at hxy
  change centralRadicalHom q s (Multiplicative.ofAdd (centralPair q s v w)) ∈ H
  change ⁅x, y⁆ = centralRadicalHom q s (Multiplicative.ofAdd (centralPair q s v w)) at hxy
  rw [← hxy]
  change x * y * x⁻¹ * y⁻¹ ∈ H
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

theorem radicalVectorImage_finrank_le (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (fixedRadical q s)) (hH : ¬ (centralRadicalHom q s).range ≤ H) :
    Module.finrank (ZMod q.prime)
      (AddSubgroup.toZModSubmodule q.prime (radicalVectorImage q s H)) ≤
        (s + 1) * q.exponent :=
  twice_finrank_le_of_centralPairing q s (radicalCentralIntersection q s H)
    (radicalCentralIntersection_ne_top q s H hH) (radicalVectorImage q s H)
    (radicalVectorImage_pairing_mem q s H)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
