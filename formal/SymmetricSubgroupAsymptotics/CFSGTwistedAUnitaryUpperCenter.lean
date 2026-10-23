import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalUpperEmbedding
import Mathlib.Tactic.Group

/-! Intrinsic centre of the ACTUAL defining-fixed upper subgroup. A
central element has trivial middle factor because its middle matrix acts
trivially on every radical vector. The remaining radical factor is in its
proved centre. This holds at q=2 as well, without a torus-weight claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem central_upper_middle_action_trivial (q : CFSG.PrimePower) (s : ℕ)
    (z : naturalUnipotent (s + 2) q) (hz : z ∈ Subgroup.center (naturalUnipotent (s + 2) q))
    (r : fixedRadical q s) (a : naturalFixed s q)
    (hfac : upperFixedHom q (s + 2) z = r.val * naturalFixedMiddleHom q s a)
    (v : Fin (s + 1) → q.Extension 2) : (a.val.val : Mat (q.Extension 2) s) *ᵥ v = v := by
  obtain ⟨h, hh⟩ := fixedRadicalParameterHom_surjective q s (Multiplicative.ofAdd v)
  have hcomm := congrArg (upperFixedHom q (s + 2))
    (Subgroup.mem_center_iff.mp hz (radicalUpperHom q s h)).symm
  change upperFixedHom q (s + 2) z * h.val = h.val * upperFixedHom q (s + 2) z at hcomm
  rw [hfac] at hcomm
  have he : radicalMiddleConjugate q s a h = r⁻¹ * h * r := by
    apply Subtype.ext
    change naturalFixedMiddleHom q s a * h.val * (naturalFixedMiddleHom q s a)⁻¹ =
      r.val⁻¹ * h.val * r.val
    calc
      _ = r.val⁻¹ * ((r.val * naturalFixedMiddleHom q s a) * h.val) *
          (naturalFixedMiddleHom q s a)⁻¹ := by group
      _ = r.val⁻¹ * (h.val * (r.val * naturalFixedMiddleHom q s a)) *
          (naturalFixedMiddleHom q s a)⁻¹ :=
        congrArg (fun g : naturalFixed (s + 2) q =>
          r.val⁻¹ * g * (naturalFixedMiddleHom q s a)⁻¹) hcomm
      _ = _ := by group
  have hp := congrArg (fixedRadicalParameterHom q s) he
  rw [fixedRadicalParameter_middle_conjugate, map_mul, map_mul, map_inv] at hp
  have hadd := congrArg Multiplicative.toAdd hp
  change (a.val.val : Mat (q.Extension 2) s) *ᵥ (fixedRadicalParameterHom q s h).toAdd =
    -(fixedRadicalParameterHom q s r).toAdd + (fixedRadicalParameterHom q s h).toAdd +
      (fixedRadicalParameterHom q s r).toAdd at hadd
  have hv : (fixedRadicalParameterHom q s h).toAdd = v := congrArg Multiplicative.toAdd hh
  rw [hv] at hadd
  have hcancel : -(fixedRadicalParameterHom q s r).toAdd + v +
      (fixedRadicalParameterHom q s r).toAdd = v := by abel
  rw [hcancel] at hadd
  exact hadd

theorem central_upper_is_centralRadical (q : CFSG.PrimePower) (s : ℕ)
    (z : naturalUnipotent (s + 2) q) (hz : z ∈ Subgroup.center (naturalUnipotent (s + 2) q)) :
    ∃ c : Multiplicative (centralParameters q s), upperCentralHom q s c = z := by
  obtain ⟨r, hfac⟩ := upper_radical_middle_factor q s z
  let a := upperFixedHom q s (middleUnipotentElement q s z)
  have ha : a = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    change (a.val.val : Mat (q.Extension 2) s) *ᵥ Pi.single i 1 =
      (1 : Mat (q.Extension 2) s) *ᵥ Pi.single i 1
    rw [Matrix.one_mulVec]
    exact central_upper_middle_action_trivial q s z hz r a hfac (Pi.single i 1)
  have hfz : upperFixedHom q (s + 2) z = r.val := by
    change upperFixedHom q (s + 2) z = r.val * naturalFixedMiddleHom q s a at hfac
    simpa only [ha, map_one, mul_one] using hfac
  have hr : r ∈ Subgroup.center (fixedRadical q s) := by
    apply Subgroup.mem_center_iff.mpr
    intro h
    apply Subtype.ext
    have he := congrArg (upperFixedHom q (s + 2))
      (Subgroup.mem_center_iff.mp hz (radicalUpperHom q s h))
    change h.val * upperFixedHom q (s + 2) z = upperFixedHom q (s + 2) z * h.val at he
    rw [hfz] at he
    exact he
  have hr0 : fixedRadicalParameterHom q s r = 1 := by
    change r ∈ (fixedRadicalParameterHom q s).ker
    rw [← fixedRadical_center_eq_kernel]
    exact hr
  obtain ⟨c, hc⟩ := exists_centralRadical_of_parameter_one q s r hr0
  refine ⟨c, ?_⟩
  apply upperFixedHom_injective q (s + 2)
  change (centralRadicalHom q s c).val = upperFixedHom q (s + 2) z
  exact (congrArg Subtype.val hc).trans hfz.symm

theorem upperCentralHom_mem_center (q : CFSG.PrimePower) (s : ℕ)
    (c : Multiplicative (centralParameters q s)) :
    upperCentralHom q s c ∈ Subgroup.center (naturalUnipotent (s + 2) q) := by
  apply Subgroup.mem_center_iff.mpr
  intro z
  obtain ⟨r, hfac⟩ := upper_radical_middle_factor q s z
  let a := upperFixedHom q s (middleUnipotentElement q s z)
  have hc : r.val * (centralRadicalHom q s c).val =
      (centralRadicalHom q s c).val * r.val :=
    congrArg (fun g : fixedRadical q s => g.val)
      (Subgroup.mem_center_iff.mp (centralRadicalHom_mem_center q s c) r)
  have hm := middle_centralRadical_commute q s a c
  apply upperFixedHom_injective q (s + 2)
  change upperFixedHom q (s + 2) z * (centralRadicalHom q s c).val =
    (centralRadicalHom q s c).val * upperFixedHom q (s + 2) z
  change upperFixedHom q (s + 2) z = r.val * naturalFixedMiddleHom q s a at hfac
  rw [hfac]
  calc
    (r.val * naturalFixedMiddleHom q s a) * (centralRadicalHom q s c).val =
        r.val * (naturalFixedMiddleHom q s a * (centralRadicalHom q s c).val) := mul_assoc _ _ _
    _ = r.val * ((centralRadicalHom q s c).val * naturalFixedMiddleHom q s a) := congrArg _ hm
    _ = (r.val * (centralRadicalHom q s c).val) * naturalFixedMiddleHom q s a := (mul_assoc _ _ _).symm
    _ = ((centralRadicalHom q s c).val * r.val) * naturalFixedMiddleHom q s a :=
      congrArg (fun t : naturalFixed (s + 2) q => t * naturalFixedMiddleHom q s a) hc
    _ = (centralRadicalHom q s c).val * (r.val * naturalFixedMiddleHom q s a) := mul_assoc _ _ _

theorem naturalUnipotent_center_eq (q : CFSG.PrimePower) (s : ℕ) :
    Subgroup.center (naturalUnipotent (s + 2) q) = (upperCentralHom q s).range := by
  apply le_antisymm
  · intro z hz
    exact central_upper_is_centralRadical q s z hz
  · rintro z ⟨c, rfl⟩
    exact upperCentralHom_mem_center q s c

theorem naturalUnipotent_center_card (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (Subgroup.center (naturalUnipotent (s + 2) q)) = q.order := by
  rw [naturalUnipotent_center_eq]
  calc
    _ = Nat.card (Multiplicative (centralParameters q s)) :=
      (Nat.card_congr (MonoidHom.ofInjective (upperCentralHom_injective q s)).toEquiv).symm
    _ = Nat.card (centralParameters q s) := Nat.card_congr Multiplicative.toAdd
    _ = q.order := centralParameters_card q s

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
