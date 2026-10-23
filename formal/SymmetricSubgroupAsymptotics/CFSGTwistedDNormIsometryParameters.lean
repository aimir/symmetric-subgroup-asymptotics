import SymmetricSubgroupAsymptotics.CFSGTwistedDNormPlaneIsometries
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormOneTorusIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularComponents

/-! The actual norm-plane isometry parameter group has at most four
cosets modulo the retained literal torus rotations. A coefficient and a
Boolean component encode the whole map; the torus fibre has checked
index at most two. No orthogonal order formula is invoked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNormIsometryParameters
open CFSGTwistedDAnisotropicNormForm CFSGTwistedDLinearParameters
open CFSGTwistedDNormOneUnits CFSGTwistedDNormOneTorusIndex CFSGTwistedA2FixedField
open CFSGTwistedDNormPlaneIsometries CFSGSerreOrdinaryTwists
open CFSGOrthogonalDIndexSingularComponents

abbrev normIsometries (q : CFSG.PrimePower) := isometryGroup (normForm q)

local instance (q : CFSG.PrimePower) : Finite (normIsometries q) :=
  Finite.of_injective (fun g : normIsometries q => (g.val : q.Extension 2 → q.Extension 2))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (fun x => congrFun h x)))

theorem mem_normOne_of_norm_one (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (hc : Algebra.norm (fixedField q) (c : q.Extension 2) = 1) : c ∈ normOneUnits q := by
  have h := congrArg (fun x : fixedField q => (x : q.Extension 2)) hc
  dsimp only at h
  rw [norm_coe] at h
  change (c : q.Extension 2) * definingFieldAutomorphism q 2 (c : q.Extension 2) = 1 at h
  change c ^ (q.order + 1) = 1
  apply Units.ext
  change (c : q.Extension 2) ^ (q.order + 1) = 1
  rw [pow_succ, ← definingFieldAutomorphism_apply]
  exact (mul_comm _ _).trans h

theorem norm_one (q : CFSG.PrimePower) (c : normOneUnits q) :
    Algebra.norm (fixedField q) (c.val : q.Extension 2) = 1 := by
  apply Subtype.ext
  rw [norm_coe, frobenius_eq_inv, mul_inv_cancel₀ (Units.ne_zero c.val)]
  rfl

def rotationHom (q : CFSG.PrimePower) : normOneUnits q →* normIsometries q where
  toFun c := ⟨Units.mulLeftLinearEquiv (fixedField q) (q.Extension 2) c.val, by
    intro a
    change normForm q ((c.val : q.Extension 2) * a) = normForm q a
    rw [normForm_apply, normForm_apply, map_mul, norm_one, one_mul]⟩
  map_one' := by
    apply Subtype.ext
    ext a
    change (1 : q.Extension 2) * a = a
    exact one_mul a
  map_mul' c d := by
    apply Subtype.ext
    ext a
    change (((c.val * d.val : (q.Extension 2)ˣ) : q.Extension 2) * a) =
      (c.val : q.Extension 2) * ((d.val : q.Extension 2) * a)
    rw [Units.val_mul, mul_assoc]

theorem rotationHom_injective (q : CFSG.PrimePower) : Function.Injective (rotationHom q) := by
  intro c d he
  have h := congrArg (fun T : normIsometries q => T.val 1) he
  change (c.val : q.Extension 2) * 1 = (d.val : q.Extension 2) * 1 at h
  simp only [mul_one] at h
  exact Subtype.ext (Units.ext h)

def coefficient (q : CFSG.PrimePower) (T : normIsometries q) : normOneUnits q :=
  ⟨Units.mk0 (T.val 1) (by
      intro he
      exact one_ne_zero (T.val.injective (he.trans T.val.map_zero.symm))),
    mem_normOne_of_norm_one q _ (by
      have h := T.property 1
      rw [normForm_apply, normForm_apply] at h
      change Algebra.norm (fixedField q) (T.val 1) = Algebra.norm (fixedField q) 1 at h
      rw [map_one (Algebra.norm (fixedField q))] at h
      exact h)⟩

theorem forms (q : CFSG.PrimePower) (T : normIsometries q) :
    (∀ a, T.val a = ((coefficient q T).val : q.Extension 2) * a) ∨
      (∀ a, T.val a = ((coefficient q T).val : q.Extension 2) * definingFieldAutomorphism q 2 a) := by
  obtain ⟨c, _, _, h⟩ := scalar_classification q T.val T.property
  have hc : c = ((coefficient q T).val : q.Extension 2) := by
    change c = T.val 1
    rcases h with h | h
    · have he := h 1
      rw [mul_one] at he
      exact he.symm
    · have he := h 1
      rw [map_one (definingFieldAutomorphism q 2), mul_one] at he
      exact he.symm
  rw [hc] at h
  exact h

theorem card_le_twice_normOne (q : CFSG.PrimePower) :
    Nat.card (normIsometries q) ≤ 2 * Nat.card (normOneUnits q) := by
  classical
  let code : normIsometries q → normOneUnits q × Bool := fun T =>
    (coefficient q T, decide (∀ a, T.val a = ((coefficient q T).val : q.Extension 2) * a))
  have hi : Function.Injective code := by
    intro T U he
    have hc : coefficient q T = coefficient q U := congrArg Prod.fst he
    have hb := congrArg Prod.snd he
    change decide (∀ a, T.val a = ((coefficient q T).val : q.Extension 2) * a) =
      decide (∀ a, U.val a = ((coefficient q U).val : q.Extension 2) * a) at hb
    have hiff := decide_eq_decide.mp hb
    apply Subtype.ext
    apply LinearEquiv.ext
    intro a
    by_cases ht : ∀ a, T.val a = ((coefficient q T).val : q.Extension 2) * a
    · exact (ht a).trans ((congrArg (fun c : normOneUnits q => (c.val : q.Extension 2) * a) hc).trans
        ((hiff.mp ht) a).symm)
    · have hT := (forms q T).resolve_left ht
      have hU := (forms q U).resolve_left (fun h => ht (hiff.mpr h))
      exact (hT a).trans
        ((congrArg (fun c : normOneUnits q => (c.val : q.Extension 2) * definingFieldAutomorphism q 2 a) hc).trans
          (hU a).symm)
  have h := Nat.card_le_card_of_injective code hi
  have hbool : Nat.card Bool = 2 := by simp
  rw [Nat.card_prod, hbool] at h
  simpa only [Nat.mul_comm] using h

def retainedRotations (q : CFSG.PrimePower) : Subgroup (normIsometries q) :=
  (retainedResidual q).map (rotationHom q)

theorem retainedRotations_index_le_four (q : CFSG.PrimePower) :
    (retainedRotations q).index ≤ 4 := by
  have hc : Nat.card (retainedRotations q) = Nat.card (retainedResidual q) :=
    (Nat.card_congr ((retainedResidual q).equivMapOfInjective
      (rotationHom q) (rotationHom_injective q)).toEquiv).symm
  have hbound : Nat.card (normIsometries q) ≤ Nat.card (retainedRotations q) * 4 := by
    calc
      Nat.card (normIsometries q) ≤ 2 * Nat.card (normOneUnits q) := card_le_twice_normOne q
      _ = 2 * (Nat.card (retainedResidual q) * (retainedResidual q).index) := by
        rw [(retainedResidual q).card_mul_index]
      _ ≤ 2 * (Nat.card (retainedResidual q) * 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (retainedResidual_index_le_two q))
      _ = Nat.card (retainedRotations q) * 4 := by rw [hc]; ring
  rw [← (retainedRotations q).card_mul_index] at hbound
  exact Nat.le_of_mul_le_mul_left hbound Nat.card_pos

end SymmetricSubgroupAsymptotics.CFSGTwistedDNormIsometryParameters
