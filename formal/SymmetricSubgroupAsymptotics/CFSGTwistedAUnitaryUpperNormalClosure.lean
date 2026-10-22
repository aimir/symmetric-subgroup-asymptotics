import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNestedRadical
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperFactorization

/-! A normal subgroup of the actual defining-fixed group containing its
outer radical contains the entire upper group. The induction is on
upper factorization INSIDE THE LARGE GROUP: small inner groups are not
asserted perfect. This includes every defining field of order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem naturalUnipotent_small_support (q : CFSG.PrimePower) (r : ℕ) (hr : r ≤ 2)
    (g : naturalUnipotent r q) :
    (∀ i, (g.val.val : Mat (q.Extension 2) r) i i = 1) ∧
    ∀ i j, i ≠ 0 → j ≠ Fin.last r →
      (g.val.val : Mat (q.Extension 2) r) i j = (1 : Mat (q.Extension 2) r) i j := by
  refine ⟨g.property.1.2, ?_⟩
  intro i j hi hj
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.one_apply, if_pos rfl] using g.property.1.2 i
  · rw [Matrix.one_apply, if_neg hij]
    apply g.property.1.1
    change j.val < i.val
    have hi0 : i.val ≠ 0 := fun he => hi (Fin.ext he)
    have hjr : j.val ≠ r := fun he => hj (Fin.ext he)
    have hval : i.val ≠ j.val := fun he => hij (Fin.ext he)
    have hib := i.isLt
    have hjb := j.isLt
    omega

theorem naturalUnipotent_zero_eq_one (q : CFSG.PrimePower) (g : naturalUnipotent 0 q) : g = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hij : i = j := (Fin.eq_zero i).trans (Fin.eq_zero j).symm
  subst j
  simpa only [Subgroup.coe_one, Units.val_one, Matrix.one_apply, if_pos rfl] using g.property.1.2 i

theorem middle_supported_mem_of_outer_le (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (naturalFixed (s + 3) q)) [H.Normal]
    (hR : fixedRadical q (s + 1) ≤ H) (g : naturalFixed (s + 1) q)
    (hd : ∀ i, (g.val.val : Mat (q.Extension 2) (s + 1)) i i = 1)
    (hs : ∀ i j, i ≠ 0 → j ≠ Fin.last (s + 1) →
      (g.val.val : Mat (q.Extension 2) (s + 1)) i j =
        (1 : Mat (q.Extension 2) (s + 1)) i j) :
    naturalFixedMiddleHom q (s + 1) g ∈ H := by
  have hu := hR (paired_conjugate_middle_supported_mem q s g hd hs)
  have hc := (inferInstance : H.Normal).conj_mem _ hu (endpointPairWeyl q s)
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hc

theorem middle_radical_mem_of_outer_le (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (naturalFixed (s + 4) q)) [H.Normal]
    (hR : fixedRadical q (s + 2) ≤ H) (g : fixedRadical q s) :
    naturalFixedMiddleHom q (s + 2) g.val ∈ H := by
  obtain ⟨hd, hs⟩ := (mem_fixedRadical_iff_natural_support q s g.val).mp g.property
  exact middle_supported_mem_of_outer_le q (s + 1) H hR g.val hd hs

theorem upper_mem_normal_of_radical_le (q : CFSG.PrimePower) (s : ℕ) :
    ∀ (H : Subgroup (naturalFixed (s + 2) q)), H.Normal → fixedRadical q s ≤ H →
      ∀ g : naturalUnipotent (s + 2) q, upperFixedHom q (s + 2) g ∈ H := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro H hnormal hR g
    letI : H.Normal := hnormal
    obtain ⟨u, hu⟩ := upper_radical_middle_factor q s g
    rw [hu]
    apply H.mul_mem (hR u.property)
    cases s with
    | zero =>
      rw [naturalUnipotent_zero_eq_one q (middleUnipotentElement q 0 g), map_one, map_one]
      exact H.one_mem
    | succ s =>
      cases s with
      | zero =>
        obtain ⟨hd, hs⟩ := naturalUnipotent_small_support q 1 (by decide)
          (middleUnipotentElement q 1 g)
        exact middle_supported_mem_of_outer_le q 0 H hR
          (upperFixedHom q 1 (middleUnipotentElement q 1 g)) hd hs
      | succ k =>
        let L : Subgroup (naturalFixed (k + 2) q) := H.comap (naturalFixedMiddleHom q (k + 2))
        have hL : L.Normal := inferInstance
        have hLR : fixedRadical q k ≤ L := by
          intro v hv
          exact middle_radical_mem_of_outer_le q k H hR ⟨v, hv⟩
        exact ih k (by omega) L hL hLR (middleUnipotentElement q (k + 2) g)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
