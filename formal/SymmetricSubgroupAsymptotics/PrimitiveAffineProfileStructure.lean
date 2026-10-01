import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationAssembly
import SymmetricSubgroupAsymptotics.AbelianMinimalNormal
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Structure forced by a primitive affine profile

The published primitive-socle dichotomy supplies a literal regular normal
`p`-subgroup.  This file derives the structural facts used by the counting
consumers from that witness itself.  In particular, no soluble-affine ledger
label or finite catalogue row is introduced here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics

namespace PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [MulAction L Ω]
  (P : PrimitiveAffineProfile L Ω)

/-- A regular normal subgroup is literally in bijection with the action
domain, by evaluation at any base point. -/
def pointEquiv (x : Ω) : P.V ≃ Ω where
  toFun v := v • x
  invFun y := Classical.choose (P.regular x y)
  left_inv v := by
    have hv := (Classical.choose_spec (P.regular x (v • x))).2 v rfl
    exact hv.symm
  right_inv y := (Classical.choose_spec (P.regular x y)).1

theorem card_eq [Finite L] [Finite Ω] (x : Ω) :
    Nat.card P.V = Nat.card Ω :=
  Nat.card_congr (P.pointEquiv x)

/-- No nonidentity translation fixes a point. -/
theorem eq_one_of_smul_eq (x : Ω) (v : P.V) (hv : v • x = x) : v = 1 := by
  exact (Classical.choose_spec (P.regular x x)).2 v hv |>.trans
    ((Classical.choose_spec (P.regular x x)).2 1 (one_smul _ _)).symm

/-- Every nontrivial ambient-normal subgroup inside the regular subgroup is
transitive, hence equals the whole regular subgroup.  This is the usual
minimal-normal step in the primitive affine theorem, proved here directly
from preprimitivity and regularity. -/
theorem minimal [Finite L] [Finite Ω] [Nonempty Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (K : Subgroup L) (hK : K.Normal) (hKV : K ≤ P.V) :
    K = ⊥ ∨ K = P.V := by
  letI : K.Normal := hK
  letI : MulAction.IsPreprimitive L Ω := hprimitive
  by_cases hKb : K = ⊥
  · exact Or.inl hKb
  right
  have hKnt : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hKb
  have hfixed : MulAction.fixedPoints K Ω ≠ Set.univ := by
    obtain ⟨k, hk⟩ := exists_ne (1 : K)
    let x : Ω := Classical.arbitrary Ω
    intro hall
    have hx : k • x = x := by
      have : x ∈ MulAction.fixedPoints K Ω := by rw [hall]; exact Set.mem_univ x
      exact this k
    have hkv : (⟨k, hKV k.2⟩ : P.V) = 1 := P.eq_one_of_smul_eq x _ hx
    apply hk
    apply Subtype.ext
    exact congrArg (fun z : P.V => (z : L)) hkv
  haveI : MulAction.IsPretransitive K Ω :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed
  apply le_antisymm hKV
  intro v hv
  let x : Ω := Classical.arbitrary Ω
  obtain ⟨k : K, hk⟩ := MulAction.exists_smul_eq K x ((⟨v, hv⟩ : P.V) • x)
  have hsame : (⟨k, hKV k.2⟩ : P.V) = ⟨v, hv⟩ := by
    have hk' :=
      (Classical.choose_spec (P.regular x ((⟨v, hv⟩ : P.V) • x))).2
        (⟨k, hKV k.2⟩ : P.V) hk
    have hv' :=
      (Classical.choose_spec (P.regular x ((⟨v, hv⟩ : P.V) • x))).2
        (⟨v, hv⟩ : P.V) rfl
    exact hk'.trans hv'.symm
  have hval : (k : L) = v := congrArg (fun z : P.V => (z : L)) hsame
  rw [← hval]
  exact k.2

/-- In a nontrivial finite primitive affine action, the regular normal
`p`-subgroup is abelian.  Its centre is nontrivial and characteristic, so
minimal normality makes the centre the whole subgroup. -/
theorem isMulCommutative [Finite L] [Finite Ω] [Nontrivial Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω) : IsMulCommutative P.V := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hVnt : Nontrivial P.V := by
    let x : Ω := Classical.arbitrary Ω
    obtain ⟨y, hy⟩ := exists_ne x
    let v : P.V := Classical.choose (P.regular x y)
    have hvxy : v • x = y := (Classical.choose_spec (P.regular x y)).1
    refine ⟨v, 1, ?_⟩
    intro hv
    apply hy
    rw [← hvxy, hv, one_smul]
  letI : Nontrivial P.V := hVnt
  have hcenterNt : (Subgroup.center P.V).map P.V.subtype ≠ ⊥ := by
    haveI : Nontrivial (Subgroup.center P.V) := P.V_pgroup.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P.V)
    intro hbot
    have hm : ((z : P.V) : L) ∈ (Subgroup.center P.V).map P.V.subtype :=
      ⟨z, z.2, rfl⟩
    rw [hbot] at hm
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.mem_bot.mp hm)
  have hcenterNormal : ((Subgroup.center P.V).map P.V.subtype).Normal := inferInstance
  have hcenterLe : (Subgroup.center P.V).map P.V.subtype ≤ P.V :=
    Subgroup.map_subtype_le _
  have hcenterEq : (Subgroup.center P.V).map P.V.subtype = P.V :=
    (P.minimal hprimitive _ hcenterNormal hcenterLe).resolve_left hcenterNt
  apply isMulCommutative_iff.mpr
  intro a b
  ·
    have ha : (a : L) ∈ (Subgroup.center P.V).map P.V.subtype := by
      rw [hcenterEq]
      exact a.2
    obtain ⟨z, hz, hza⟩ := ha
    have hzb : z * b = b * z := ((Subgroup.mem_center_iff.mp hz) b).symm
    apply Subtype.ext
    simpa [← hza] using congrArg Subtype.val hzb

/-- The regular subgroup is elementary abelian at its profile prime.  This
is the exact vector-space chart needed before constructing affine counting
certificates. -/
theorem elementary [Finite L] [Finite Ω] [Nontrivial Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω) :
    letI : Fact P.p.Prime := ⟨P.p_prime⟩
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod P.p) V)
      (_ : FiniteDimensional (ZMod P.p) V),
      Nonempty (P.V ≃* Multiplicative V) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  have hmin : ∀ K : Subgroup L, K.Normal → K ≤ P.V → K = ⊥ ∨ K = P.V :=
    fun K hK hKV => P.minimal hprimitive K hK hKV
  rcases abelian_minimal_normal_elementary_or_coprime P.V P.p hmin with h | h
  · exact h
  · have hVnt : Nontrivial P.V := by
      let x : Ω := Classical.arbitrary Ω
      obtain ⟨y, hy⟩ := exists_ne x
      let v : P.V := Classical.choose (P.regular x y)
      have hvxy : v • x = y := (Classical.choose_spec (P.regular x y)).1
      refine ⟨v, 1, ?_⟩
      intro hv
      apply hy
      rw [← hvxy, hv, one_smul]
    letI : Nontrivial P.V := hVnt
    obtain ⟨n, hnpos, hn⟩ := P.V_pgroup.nontrivial_iff_card.mp inferInstance
    have hpdiv : P.p ∣ Nat.card P.V := by
      rw [hn]
      exact dvd_pow_self P.p hnpos.ne'
    exact False.elim ((P.p_prime.coprime_iff_not_dvd.mp h.symm) hpdiv)

/-! ## The point-stabilizer complement -/

/-- The canonical complement attached to a chosen affine origin. -/
abbrev complement (_P : PrimitiveAffineProfile L Ω) (x : Ω) : Subgroup L :=
  MulAction.stabilizer L x

/-- The regular subgroup and the point stabilizer are exact complements. -/
theorem isComplement'_complement (x : Ω) :
    P.V.IsComplement' (P.complement x) := by
  apply Subgroup.isComplement'_stabilizer x
  · intro v hv
    exact P.eq_one_of_smul_eq x v hv
  · intro g
    let v : P.V := Classical.choose (P.regular (g • x) x)
    exact ⟨v, (Classical.choose_spec (P.regular (g • x) x)).1⟩

/-- The literal ambient group is the internal semidirect product of the
regular subgroup by the point stabilizer. -/
noncomputable def semidirectEquiv (x : Ω) :
    P.V ⋊[(P.V.normalizerMonoidHom).comp
      (Subgroup.inclusion (P.V.normalizer_eq_top ▸ le_top))]
      P.complement x ≃* L :=
  SemidirectProduct.mulEquivSubgroup (P.isComplement'_complement x)

/-- Conjugation by the point stabilizer on the translation subgroup. -/
def complementAction (x : Ω) : P.complement x →* MulAut P.V :=
  (P.V.normalizerMonoidHom).comp
    (Subgroup.inclusion (P.V.normalizer_eq_top ▸ le_top))

/-- For a faithful affine action, the point stabilizer acts faithfully on
the regular subgroup by conjugation. -/
theorem complementAction_injective [FaithfulSMul L Ω] (x : Ω) :
    Function.Injective (P.complementAction x) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
  intro y
  let v : P.V := Classical.choose (P.regular x y)
  have hvy : v • x = y := (Classical.choose_spec (P.regular x y)).1
  change (v : L) • x = y at hvy
  have hfix : (h : L) • x = x := h.2
  have hconj :
      (h : L) * (v : L) * (h : L)⁻¹ = (v : L) := by
    have hv := DFunLike.congr_fun hh v
    exact congrArg Subtype.val hv
  have hcomm : (h : L) * (v : L) = (v : L) * (h : L) := by
    calc
      (h : L) * (v : L) = ((h : L) * (v : L) * (h : L)⁻¹) * (h : L) := by group
      _ = (v : L) * (h : L) := by rw [hconj]
  calc
    (h : L) • y = (h : L) • ((v : L) • x) := by rw [hvy]
    _ = ((h : L) * (v : L)) • x := (mul_smul _ _ _).symm
    _ = ((v : L) * (h : L)) • x := by rw [hcomm]
    _ = (v : L) • ((h : L) • x) := by rw [mul_smul]
    _ = y := by rw [hfix]; exact hvy
    _ = (1 : L) • y := (one_smul L y).symm

/-- The complement is no larger than the automorphism group of the regular
subgroup. -/
theorem complement_card_le_mulEquiv [Finite L] [FaithfulSMul L Ω] (x : Ω) :
    Nat.card (P.complement x) ≤ Nat.card (P.V ≃* P.V) := by
  exact Nat.card_le_card_of_injective (P.complementAction x)
    (P.complementAction_injective x)

include P

/-- A catalogue-free order bound for every finite faithful affine profile.
It is deliberately stated using only the domain cardinality and is the
input to the large-degree SO numerical cutoff. -/
theorem card_le_domain_pow_log [Finite L] [Finite Ω] [FaithfulSMul L Ω]
    (x : Ω) :
    Nat.card L ≤ Nat.card Ω * Nat.card Ω ^ Nat.log 2 (Nat.card Ω) := by
  have hfactor := (isComplement'_complement P x).card_mul
  have hcomp := (P.complement_card_le_mulEquiv x).trans
    (Non2UnipotentPrefixFiniteMenu.mulEquiv_card_le_card_pow_log P.V)
  calc
    Nat.card L = Nat.card P.V * Nat.card (P.complement x) := hfactor.symm
    _ ≤ Nat.card P.V *
        (Nat.card P.V ^ Nat.log 2 (Nat.card P.V)) :=
      Nat.mul_le_mul_left _ hcomp
    _ = Nat.card Ω * Nat.card Ω ^ Nat.log 2 (Nat.card Ω) := by
      rw [P.card_eq x]

end PrimitiveAffineProfile

end SymmetricSubgroupAsymptotics

end
