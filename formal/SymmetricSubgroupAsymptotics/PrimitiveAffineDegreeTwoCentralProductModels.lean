import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCentralProductSummed
import SymmetricSubgroupAsymptotics.CentralBinaryProductNormalAxes
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoThreePairsEasySource
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveLin

/-!
# The literal `A4 × C2` and `S4 × C2` three-pair models

This file supplies the group-specific input to the source-summed theorem.
The checked `CentralBinaryProductCore` dichotomy is used literally.  An axis
outside the interval above the Klein layer lies in the central `C2`, hence
is either the bottom or the whole central axis.  Those two quotients are the
original product and its first factor; both are controlled on the joint cold
source.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev A4 := NaturalA4ScalarFourHead.G
private abbrev S4 := Equiv.Perm (Fin 4)

namespace CentralBinaryProductModels

/-- Projection to both factors injects epimorphisms to a direct product into
an epimorphism to the first factor and an arbitrary binary character. -/
theorem epi_prod_two_le {J L : Type*} [Group J] [Finite J]
    [Group L] [Finite L] :
    Nat.card (GroupEpimorphism J (L × C2)) ≤
      Nat.card (GroupEpimorphism J L) * Nat.card (J →* C2) := by
  let f : GroupEpimorphism J (L × C2) →
      GroupEpimorphism J L × (J →* C2) := fun φ =>
    (⟨(MonoidHom.fst L C2).comp φ.1, fun x => by
      obtain ⟨j, hj⟩ := φ.2 (x, 1)
      exact ⟨j, congrArg Prod.fst hj⟩⟩,
      (MonoidHom.snd L C2).comp φ.1)
  have hf : Function.Injective f := by
    intro φ ψ h
    apply Subtype.ext
    ext j
    · exact DFunLike.congr_fun (congrArg (fun z => z.1.1) h) j
    · exact DFunLike.congr_fun (congrArg (fun z => z.2) h) j
  calc
    Nat.card (GroupEpimorphism J (L × C2)) ≤
        Nat.card (GroupEpimorphism J L × (J →* C2)) :=
      Nat.card_le_card_of_injective f hf
    _ = _ := Nat.card_prod _ _

/-- The binary character factor on a cold source. -/
theorem hom_two_cold {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬ BinaryRankHot (51 / 200) J) :
    (Nat.card (J →* C2) : ℝ) ≤
      (2 : ℝ) ^ ((51 / 200 : ℝ) * b) := by
  unfold BinaryRankHot at hJ
  rw [binaryAbelianizationGroupHom_card]
  simp only [Module.finrank_self, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact le_of_not_gt hJ

/-- A subgroup of the literal central binary axis is bottom or the entire
axis. -/
theorem eq_bot_or_central_of_le
    {L : Type*} [Group L] (D : CentralBinaryProductCore L)
    (N : Subgroup (L × C2)) (hN : N ≤ D.central) :
    N = ⊥ ∨ N = D.central := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  apply le_antisymm hN
  obtain ⟨⟨n, hn⟩, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have hnfirst : (n : L × C2).1 = 1 := (D.mem_central n).mp (hN hn)
  have hnsecond : (n : L × C2).2 ≠ 1 := by
    intro h
    apply hn1
    exact Subtype.ext (Prod.ext hnfirst h)
  intro z hz
  have hzfirst : (z : L × C2).1 = 1 := (D.mem_central z).mp hz
  rcases C2Wreath.cases (z : L × C2).2 with hz2 | hz2
  · have hz1 : (z : L × C2) = 1 := Prod.ext hzfirst hz2
    rw [hz1]
    exact N.one_mem
  · have hn2 : (n : L × C2).2 = C2Wreath.gen := by
      rcases C2Wreath.cases (n : L × C2).2 with h | h
      · exact absurd h hnsecond
      · exact h
    have hzn : (z : L × C2) = n := Prod.ext (hzfirst.trans hnfirst.symm)
      (hz2.trans hn2.symm)
    exact hzn ▸ hn

theorem central_eq_ker_fst {L : Type*} [Group L]
    (D : CentralBinaryProductCore L) :
    D.central = (MonoidHom.fst L C2).ker := by
  ext x
  rw [D.mem_central, MonoidHom.mem_ker]
  change x.1 = 1 ↔ x.1 = 1
  rfl

/-- The quotient by the whole central factor is the first factor. -/
def quotientCentralEquiv {L : Type*} [Group L]
    (D : CentralBinaryProductCore L) :
    ((L × C2) ⧸ D.central) ≃* L :=
  (QuotientGroup.quotientMulEquivOfEq (central_eq_ker_fst D)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (MonoidHom.fst L C2) Prod.fst_surjective)

/-- Transport a cold estimate for the first factor to either of the two
lower central axes. -/
theorem lower_axis_cold
    {L : Type*} [Group L] [Finite L]
    (D : CentralBinaryProductCore L)
    (K : ℝ) (hK : 0 ≤ K)
    (firstCold : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))),
      ¬ CentralProductRankHot b J →
        (Nat.card (GroupEpimorphism J L) : ℝ) ≤
          K * (2 : ℝ) ^ ((1 / 3 : ℝ) * b))
    (N : {N : Subgroup (L × C2) // N.Normal})
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hN : ¬ D.core ≤ N.1) (hJ : ¬ CentralProductRankHot b J) :
    (Nat.card (GroupEpimorphism J ((L × C2) ⧸ N.1)) : ℝ) ≤
      K * (2 : ℝ) ^ ((3 / 5 : ℝ) * b) := by
  rcases D.normal_contains_core_or_le_central N.1 N.2 with hcore | hcentral
  · exact absurd hcore hN
  rcases eq_bot_or_central_of_le D N.1 hcentral with hbot | hcentralEq
  · have hfirst := firstCold J hJ
    have hhom := hom_two_cold J (not_or.mp hJ).1
    have hprod : (Nat.card (GroupEpimorphism J (L × C2)) : ℝ) ≤
        (Nat.card (GroupEpimorphism J L) : ℝ) * Nat.card (J →* C2) := by
      exact_mod_cast epi_prod_two_le (J := J) (L := L)
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans
        QuotientGroup.quotientBot)]
    calc
      (Nat.card (GroupEpimorphism J (L × C2)) : ℝ) ≤
          (Nat.card (GroupEpimorphism J L) : ℝ) * Nat.card (J →* C2) :=
        hprod
      _ ≤ (K * (2 : ℝ) ^ ((1 / 3 : ℝ) * b)) *
          (2 : ℝ) ^ ((51 / 200 : ℝ) * b) :=
        mul_le_mul hfirst hhom (Nat.cast_nonneg _) (by positivity)
      _ ≤ K * (2 : ℝ) ^ ((3 / 5 : ℝ) * b) := by
        rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply mul_le_mul_of_nonneg_left _ hK
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hb : (0 : ℝ) ≤ b := by positivity
        nlinarith
  · rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      ((QuotientGroup.quotientMulEquivOfEq hcentralEq).trans
        (quotientCentralEquiv D))]
    exact (firstCold J hJ).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have hb : (0 : ℝ) ≤ b := by positivity
        nlinarith)) hK)

/-! ## The two natural cores -/

/-- Transport the intrinsic core through an abstract group equivalence. -/
noncomputable def mapCoreEquiv
    {L L' : Type*} [Group L] [Group L']
    (D : CentralBinaryProductCore L) (e : L ≃* L') :
    CentralBinaryProductCore L' := by
  letI : (D.V.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map (show D.V.Normal from inferInstance)
      e.toMonoidHom e.surjective
  exact {
  V := D.V.map e.toMonoidHom
  minimal := by
    intro W hW hWV
    let W0 := W.comap e.toMonoidHom
    have hW0 : W0.Normal := Subgroup.Normal.comap hW e.toMonoidHom
    have hW0V : W0 ≤ D.V := by
      intro x hx
      have hex : e x ∈ D.V.map e.toMonoidHom := hWV hx
      simpa only [Subgroup.mem_map_equiv, e.symm_apply_apply] using hex
    have hmapW0 : W0.map e.toMonoidHom = W := by
      dsimp only [W0]
      exact Subgroup.map_comap_eq_self_of_surjective
        (f := e.toMonoidHom) e.surjective W
    rcases D.minimal W0 hW0 hW0V with hbot | hV
    · left
      have hmapped := congrArg (Subgroup.map e.toMonoidHom) hbot
      rw [hmapW0, Subgroup.map_bot] at hmapped
      exact hmapped
    · right
      have hmapped := congrArg (Subgroup.map e.toMonoidHom) hV
      rw [hmapW0] at hmapped
      exact hmapped
  selfCentralizing := by
    intro x hx
    have hx' : e.symm x ∈ D.V := by
      apply D.selfCentralizing
      intro v hv
      have h := hx (e v) ((Subgroup.mem_map_equiv).mpr (by simpa using hv))
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply, e.symm_apply_apply] using h
    exact (Subgroup.mem_map_equiv).mpr hx'
  noFixed := by
    intro v hv hcomm
    have hv' : e.symm v ∈ D.V := (Subgroup.mem_map_equiv).mp hv
    have hfix : ∀ x : L, x * e.symm v = e.symm v * x := by
      intro x
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply, e.symm_apply_apply] using hcomm (e x)
    have hv1 := D.noFixed (e.symm v) hv' hfix
    calc
      v = e (e.symm v) := (e.apply_symm_apply v).symm
      _ = e 1 := congrArg e hv1
      _ = 1 := e.map_one
  }

/-- The concrete subgroup called `a4` in the finite permutation files is
the Mathlib alternating group used by the scalar-head source. -/
theorem naturalA4_eq_alternating :
    NaturalS4.a4 = (alternatingGroup (Fin 4) : Subgroup (Equiv.Perm (Fin 4))) := by
  ext x
  rw [Equiv.Perm.mem_alternatingGroup]
  change x ∈ NaturalS4.a4Set ↔ Equiv.Perm.sign x = 1
  exact (show ∀ y : Equiv.Perm (Fin 4),
    y ∈ NaturalS4.a4Set ↔ Equiv.Perm.sign y = 1 by decide) x

def naturalA4Equiv : NaturalS4.a4 ≃* A4 :=
  MulEquiv.subgroupCongr naturalA4_eq_alternating

def naturalA4Core : CentralBinaryProductCore NaturalS4.a4 where
  V := LinearThree.kleinA4
  minimal := LinearThree.kleinA4_minimal
  selfCentralizing := LinearThree.kleinA4_selfCentralizing
  noFixed := by
    intro v hv hcomm
    let t : NaturalS4.a4 := ⟨NaturalS4.t3, NaturalS4.t3_mem_a4Set⟩
    have ht : NaturalS4.t3 * (v : Equiv.Perm (Fin 4)) * NaturalS4.t3⁻¹ = v := by
      have h := congrArg Subtype.val (hcomm t)
      change NaturalS4.t3 * (v : Equiv.Perm (Fin 4)) =
        (v : Equiv.Perm (Fin 4)) * NaturalS4.t3 at h
      rw [h]
      simp
    exact Subtype.ext (NaturalS4.t3_fixedPointFree _ hv ht)

def a4Core : CentralBinaryProductCore A4 :=
  mapCoreEquiv naturalA4Core naturalA4Equiv

/-- The transported natural Klein layer is the kernel of the concrete
cyclic-three quotient. -/
theorem a4Core_eq_topKernel :
    a4Core.V = NaturalA4ScalarFourHead.top.ker := by
  have hforward : a4Core.V ≤ NaturalA4ScalarFourHead.top.ker := by
    intro v hv
    rw [MonoidHom.mem_ker]
    change v ∈ Subgroup.map naturalA4Equiv.toMonoidHom
      LinearThree.kleinA4 at hv
    have hv' : naturalA4Equiv.symm v ∈ LinearThree.kleinA4 :=
      (Subgroup.mem_map_equiv).mp hv
    have hv2perm := NaturalS4.kleinSet_sq
      (naturalA4Equiv.symm v : Equiv.Perm (Fin 4)) hv'
    have hv2' : naturalA4Equiv.symm v ^ 2 = 1 := Subtype.ext hv2perm
    have hv2 : v ^ 2 = 1 := by
      apply naturalA4Equiv.symm.injective
      simpa only [map_pow, map_one, naturalA4Equiv.symm_apply_apply] using hv2'
    have htop2 : NaturalA4ScalarFourHead.top v ^ 2 = 1 := by
      rw [← map_pow, hv2, map_one]
    exact (show ∀ z : CyclicThree, z ^ 2 = 1 → z = 1 by decide)
      _ htop2
  apply le_antisymm hforward
  · intro x hx
    apply a4Core.selfCentralizing
    intro v hv
    letI : IsKleinFour NaturalA4ScalarFourHead.top.ker := by
      rw [NaturalA4ScalarFourHead.top_ker]
      exact alternatingGroup.kleinFour_isKleinFour (by simp)
    let hmulcomm : IsMulCommutative NaturalA4ScalarFourHead.top.ker :=
      IsKleinFour.isMulCommutative
    have hcomm :
        (⟨x, hx⟩ : NaturalA4ScalarFourHead.top.ker) *
            ⟨v, hforward hv⟩ =
          ⟨v, hforward hv⟩ * ⟨x, hx⟩ :=
      hmulcomm.is_comm.comm _ _
    exact congrArg Subtype.val hcomm

def s4Core : CentralBinaryProductCore S4 where
  V := NaturalS4.klein
  minimal := NaturalS4.klein_minimal
  selfCentralizing := NaturalS4.klein_selfCentralizing
  noFixed := by
    intro v hv hcomm
    have ht : NaturalS4.t3 * v * NaturalS4.t3⁻¹ = v := by
      rw [hcomm NaturalS4.t3]
      simp
    exact NaturalS4.t3_fixedPointFree v hv ht

/-! ## Comparator actions -/

def a4ProductTop : A4 × C2 →* CyclicThree × C2 :=
  NaturalA4ScalarFourHead.top.prodMap (MonoidHom.id C2)

theorem a4ProductTop_surjective : Function.Surjective a4ProductTop :=
  by
    rintro ⟨a, c⟩
    obtain ⟨x, rfl⟩ := NaturalA4ScalarFourHead.top_surjective a
    exact ⟨(x, c), rfl⟩

theorem a4ProductTop_ker : a4ProductTop.ker = a4Core.core := by
  ext x
  rw [MonoidHom.mem_ker, CentralBinaryProductCore.mem_core]
  change (NaturalA4ScalarFourHead.top x.1, x.2) = 1 ↔
    x.1 ∈ a4Core.V ∧ x.2 = 1
  constructor
  · intro h
    constructor
    · rw [a4Core_eq_topKernel, MonoidHom.mem_ker]
      exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · rintro ⟨hx, hsnd⟩
    apply Prod.ext
    · change NaturalA4ScalarFourHead.top x.1 = 1
      rw [← MonoidHom.mem_ker, ← a4Core_eq_topKernel]
      exact hx
    · exact hsnd

def a4QuotientTopEquiv : ((A4 × C2) ⧸ a4Core.core) ≃*
    CyclicThree × C2 :=
  (QuotientGroup.quotientMulEquivOfEq a4ProductTop_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective a4ProductTop
      a4ProductTop_surjective)

def a4QuotientAction : ((A4 × C2) ⧸ a4Core.core) →*
    Equiv.Perm (Fin 5) :=
  cyclicSixComparatorAction.comp a4QuotientTopEquiv.toMonoidHom

theorem a4QuotientAction_injective : Function.Injective a4QuotientAction := by
  exact cyclicSixComparatorAction_injective.comp a4QuotientTopEquiv.injective

def s4ProductTop : S4 × C2 →* Equiv.Perm (Fin 3) × C2 :=
  NaturalS4.pairing.prodMap (MonoidHom.id C2)

theorem s4ProductTop_surjective : Function.Surjective s4ProductTop :=
  by
    rintro ⟨a, c⟩
    obtain ⟨x, rfl⟩ := NaturalS4.pairing_surjective a
    exact ⟨(x, c), rfl⟩

theorem s4ProductTop_ker : s4ProductTop.ker = s4Core.core := by
  ext x
  rw [MonoidHom.mem_ker, CentralBinaryProductCore.mem_core]
  change (NaturalS4.pairing x.1, x.2) = 1 ↔
    x.1 ∈ NaturalS4.klein ∧ x.2 = 1
  constructor
  · intro h
    constructor
    · rw [← NaturalS4.ker_pairing, MonoidHom.mem_ker]
      exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · rintro ⟨hfst, hsnd⟩
    apply Prod.ext
    · change NaturalS4.pairing x.1 = 1
      apply MonoidHom.mem_ker.mp
      rw [NaturalS4.ker_pairing]
      exact hfst
    · exact hsnd

def s4QuotientTopEquiv : ((S4 × C2) ⧸ s4Core.core) ≃*
    Equiv.Perm (Fin 3) × C2 :=
  (QuotientGroup.quotientMulEquivOfEq s4ProductTop_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective s4ProductTop
      s4ProductTop_surjective)

def s4QuotientAction : ((S4 × C2) ⧸ s4Core.core) →*
    Equiv.Perm (Fin 5) :=
  s3c2Action.comp s4QuotientTopEquiv.toMonoidHom

theorem s4QuotientAction_injective : Function.Injective s4QuotientAction := by
  exact s3c2Action_injective.comp s4QuotientTopEquiv.injective

/-! ## Cold first-factor estimates -/

theorem a4_first_cold {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬ CentralProductRankHot b J) :
    (Nat.card (GroupEpimorphism J A4) : ℝ) ≤
      156 * (2 : ℝ) ^ ((1 / 3 : ℝ) * b) :=
  NaturalA4RankTail.bottom_epi_cold J (not_or.mp hJ).2

def s4ColdConstant : ℝ := 2 * Nat.card (S4 ≃* S4)

theorem s4ColdConstant_nonneg : 0 ≤ s4ColdConstant := by
  exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)

theorem s4_first_cold {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    (_hJ : ¬ CentralProductRankHot b J) :
    (Nat.card (GroupEpimorphism J S4) : ℝ) ≤
      s4ColdConstant * (2 : ℝ) ^ ((1 / 3 : ℝ) * b) := by
  have h := NaturalS4.epi_card_le J
  calc
    _ ≤ (2 * Nat.card (S4 ≃* S4) : ℝ) *
        (2 : ℝ) ^ ((1 / 4 : ℝ) * b) := h
    _ ≤ s4ColdConstant * (2 : ℝ) ^ ((1 / 3 : ℝ) * b) := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          have hb : (0 : ℝ) ≤ b := by positivity
          nlinarith))
      exact s4ColdConstant_nonneg

/-- The exact `A4 × C2` quotient package. -/
noncomputable def a4TimesTwo :
    PreE7CentralProductRankTailData (A4 × C2) where
  E := a4Core.core
  action := a4QuotientAction
  action_injective := a4QuotientAction_injective
  lowerConstant := 156
  lowerConstant_nonneg := by norm_num
  lower_axis_cold := lower_axis_cold a4Core 156 (by norm_num)
    (fun J hJ => a4_first_cold J hJ)
  order_le := by
    rw [Nat.card_prod, alternatingGroup.card_of_card_eq_four (by simp)]
    norm_num [C2]

/-- The exact `S4 × C2` quotient package. -/
noncomputable def s4TimesTwo :
    PreE7CentralProductRankTailData (S4 × C2) where
  E := s4Core.core
  action := s4QuotientAction
  action_injective := s4QuotientAction_injective
  lowerConstant := s4ColdConstant
  lowerConstant_nonneg := s4ColdConstant_nonneg
  lower_axis_cold := lower_axis_cold s4Core s4ColdConstant
    s4ColdConstant_nonneg (fun J hJ => s4_first_cold J hJ)
  order_le := by
    rw [Nat.card_prod, Nat.card_perm, Nat.card_fin]
    norm_num [C2]

end CentralBinaryProductModels

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
