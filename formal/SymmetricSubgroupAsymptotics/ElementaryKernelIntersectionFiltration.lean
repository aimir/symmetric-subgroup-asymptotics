import SymmetricSubgroupAsymptotics.OriginalKernelCenter
import SymmetricSubgroupAsymptotics.SchurTargetExtension
import SymmetricSubgroupAsymptotics.SchurRepresentation
import Mathlib.Algebra.Module.ZMod

/-!
# An elementary normal kernel filtered by another original quotient

For an actual elementary normal kernel `A` in `Q`, a second original map
`pi` cuts out the literal intersection `A ∩ ker pi`. Its original
conjugation representation injects into any displayed module chart of
`ker pi`. The remaining vector quotient has cardinality exactly the
actual image of `A` under `pi`; no splitting of either group extension
is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace OriginalKernelModuleChart

variable {Q B D : Type} [Group Q] [Group B] [Group D]
  {eta : Q →* D} {A : Rep (ZMod 2) D}
  (E : OriginalKernelModuleChart eta A) (pi : Q →* B)

def elementaryImageHom : Multiplicative A →* B :=
  pi.comp (eta.ker.subtype.comp E.equiv.toMonoidHom)

def kernelIntersection : Subrepresentation (inflatedRepresentation eta A.ρ) where
  toSubmodule := AddSubgroup.toZModSubmodule 2
    (Subgroup.toAddSubgroup' (E.elementaryImageHom pi).ker)
  apply_mem_toSubmodule := by
    intro g v hv
    change pi (E.element v) = 1 at hv
    change pi (E.element (A.ρ (eta g) v)) = 1
    rw [show E.element (A.ρ (eta g) v) = g * E.element v * g⁻¹ from E.conjugate g v,
      map_mul, map_mul, map_inv, hv, mul_one, mul_inv_cancel]

@[simp] theorem mem_kernelIntersection (v : A) :
    v ∈ E.kernelIntersection pi ↔ pi (E.element v) = 1 := Iff.rfl

def kernelIntersectionHom :
    Multiplicative (E.kernelIntersection pi).toSubmodule →* pi.ker where
  toFun v := ⟨E.element v.toAdd.val, v.toAdd.property⟩
  map_one' := by
    apply Subtype.ext
    change (E.equiv 1 : Q) = 1
    simp only [map_one, OneMemClass.coe_one]
  map_mul' v w := by
    apply Subtype.ext
    exact originalKernelChart_add eta A E v.toAdd.val w.toAdd.val

variable {K : Rep (ZMod 2) B} (F : OriginalKernelModuleChart pi K)

def kernelIntersectionToModule :
    (E.kernelIntersection pi).toSubmodule →ₗ[ZMod 2] K :=
  (show (E.kernelIntersection pi).toSubmodule →+ K from
    { toFun := fun v ↦
        (F.equiv.symm (E.kernelIntersectionHom pi (Multiplicative.ofAdd v))).toAdd
      map_zero' := congrArg Multiplicative.toAdd
        (map_one (F.equiv.symm.toMonoidHom.comp (E.kernelIntersectionHom pi)))
      map_add' := fun v w ↦ congrArg Multiplicative.toAdd
        (map_mul (F.equiv.symm.toMonoidHom.comp (E.kernelIntersectionHom pi))
          (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }).toZModLinearMap 2

theorem kernelIntersectionToModule_element
    (v : (E.kernelIntersection pi).toSubmodule) :
    F.element (E.kernelIntersectionToModule pi F v) = E.element v.val := by
  exact congrArg (fun z : pi.ker ↦ (z : Q))
    (F.equiv.apply_symm_apply (E.kernelIntersectionHom pi (Multiplicative.ofAdd v)))

/-- The literal intersection embeds in the second original kernel chart. -/
def kernelIntersectionIntertwiner :
    (E.kernelIntersection pi).toRepresentation.IntertwiningMap
      (inflatedRepresentation pi K.ρ) where
  toLinearMap := E.kernelIntersectionToModule pi F
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro v
    apply F.element_injective
    calc
      F.element (E.kernelIntersectionToModule pi F
          ((E.kernelIntersection pi).toRepresentation g v)) =
          E.element (A.ρ (eta g) v.val) := E.kernelIntersectionToModule_element pi F _
      _ = g * E.element v.val * g⁻¹ := E.conjugate g v.val
      _ = g * F.element (E.kernelIntersectionToModule pi F v) * g⁻¹ := by
        rw [E.kernelIntersectionToModule_element]
      _ = F.element (K.ρ (pi g) (E.kernelIntersectionToModule pi F v)) :=
        (F.conjugate g _).symm

theorem kernelIntersectionIntertwiner_injective :
    Function.Injective (E.kernelIntersectionIntertwiner pi F) := by
  intro v w h
  apply Subtype.ext
  apply E.element_injective
  have hh : F.element (E.kernelIntersectionToModule pi F v) =
      F.element (E.kernelIntersectionToModule pi F w) := congrArg F.element h
  rw [E.kernelIntersectionToModule_element pi F v,
    E.kernelIntersectionToModule_element pi F w] at hh
  exact hh

omit F in
def kernelImageRepresentation :
    Representation (ZMod 2) Q (A ⧸ (E.kernelIntersection pi).toSubmodule) :=
  (inflatedRepresentation eta A.ρ).quotient (E.kernelIntersection pi).toSubmodule
    (fun g ↦ (E.kernelIntersection pi).apply_mem_toSubmodule g)

omit F in
def kernelImageProjection :
    (inflatedRepresentation eta A.ρ).IntertwiningMap (E.kernelImageRepresentation pi) where
  toLinearMap := (E.kernelIntersection pi).toSubmodule.mkQ
  isIntertwining' _ := rfl

omit F in
theorem kernelImageProjection_surjective : Function.Surjective (E.kernelImageProjection pi) :=
  (E.kernelIntersection pi).toSubmodule.mkQ_surjective

omit F in
theorem kernelImageProjection_ker :
    (E.kernelImageProjection pi).ker = E.kernelIntersection pi := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.ker_mkQ _

omit F in
/-- Scalar quotient cardinality equals the actual multiplicative image. -/
theorem kernelImage_card [Finite A] :
    Nat.card (A ⧸ (E.kernelIntersection pi).toSubmodule) =
      Nat.card (E.elementaryImageHom pi).range := by
  let S := (E.kernelIntersection pi).toSubmodule
  let f := E.elementaryImageHom pi
  let e : f.ker ≃ S :=
    { toFun := fun v ↦ ⟨v.val.toAdd, v.property⟩
      invFun := fun v ↦ ⟨Multiplicative.ofAdd v.val, v.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hg : Nat.card S * Nat.card f.range = Nat.card A := by
    have h := f.ker.card_mul_index
    rw [Subgroup.index_ker, Nat.card_congr e,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative A ≃ A)] at h
    exact h
  have hv : Nat.card S * Nat.card (A ⧸ S) = Nat.card A := by
    have hS : Nat.card S = 2 ^ Module.finrank (ZMod 2) S := by
      simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S)
    have hquot : Nat.card (A ⧸ S) = 2 ^ Module.finrank (ZMod 2) (A ⧸ S) := by
      simpa only [Nat.card_zmod] using
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A ⧸ S)
    have hA : Nat.card A = 2 ^ Module.finrank (ZMod 2) A := by
      simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A)
    rw [hS, hquot, hA, ← pow_add, Nat.add_comm, S.finrank_quotient_add_finrank]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hv.trans hg.symm)

omit F in
/-- Only four binary dimensions can survive in an image whose group
order divides forty-eight. The same argument works for every binary
exponent with a single odd factor three. -/
theorem kernelImage_finrank_le [Finite A] [Finite B] {d : ℕ}
    (hcard : Nat.card B ∣ 2 ^ d * 3) :
    Module.finrank (ZMod 2) (A ⧸ (E.kernelIntersection pi).toSubmodule) ≤ d := by
  let n := Module.finrank (ZMod 2) (A ⧸ (E.kernelIntersection pi).toSubmodule)
  have hpow : 2 ^ n ∣ 2 ^ d * 3 := by
    have h := (E.elementaryImageHom pi).range.card_subgroup_dvd_card.trans hcard
    rw [← E.kernelImage_card pi, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod] at h
    exact h
  have hcop : Nat.Coprime (2 ^ n) 3 := (by decide : Nat.Coprime 2 3).pow_left n
  have hdiv : 2 ^ n ∣ 2 ^ d := hcop.dvd_mul_right.mp hpow
  exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))).mp hdiv

end OriginalKernelModuleChart
end SymmetricSubgroupAsymptotics

end
