import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPoleShearElementary
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryCenter
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! The whole odd-B point radical is retained in the actual elementary
group and its actual central quotient. Its projective injection uses the
literal normalized opposite pole, not an assumed unipotent model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalHom

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOddPoleCoordinates
open CFSGOrthogonalBOddPoleShear CFSGOrthogonalBOddPoleShearElementary
open CFSGOrthogonalBOddQuadraticForm CFSGQuadraticHyperbolicShear
variable (K : Type) [Field K] [Finite K]

private theorem element_ext (s : ℕ) (g h : elementaryRootGroup K (s + 3))
    (he : ∀ v : Index (s + 3) → K,
      (g.val : Mat K (s + 3)) *ᵥ v = (h.val : Mat K (s + 3)) *ᵥ v) : g = h := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hh := congrFun (he (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hh

def radicalElement (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : Index (s + 2) → K) : elementaryRootGroup K (s + 3) :=
  Classical.choose (poleShear_has_element K h2 s z)

theorem radicalElement_apply (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : Index (s + 2) → K) (v : Index (s + 3) → K) :
    ((radicalElement K h2 s z).val : Mat K (s + 3)) *ᵥ v =
      poleShear K h2 (s + 2) z v :=
  Classical.choose_spec (poleShear_has_element K h2 s z) v

def radicalHom (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Multiplicative (Index (s + 2) → K) →* elementaryRootGroup K (s + 3) where
  toFun z := radicalElement K h2 s z.toAdd
  map_one' := by
    apply element_ext K s
    intro v
    change ((radicalElement K h2 s 0).val : Mat K (s + 3)) *ᵥ v =
      (1 : Mat K (s + 3)) *ᵥ v
    rw [radicalElement_apply, poleShear_zero_apply, Matrix.one_mulVec]
  map_mul' z t := by
    apply element_ext K s
    intro v
    change ((radicalElement K h2 s (z.toAdd + t.toAdd)).val : Mat K (s + 3)) *ᵥ v =
      (((radicalElement K h2 s z.toAdd).val : Mat K (s + 3)) *
        ((radicalElement K h2 s t.toAdd).val : Mat K (s + 3))) *ᵥ v
    rw [← Matrix.mulVec_mulVec, radicalElement_apply, radicalElement_apply,
      radicalElement_apply, poleShear_add_apply]

theorem radicalHom_apply (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : Multiplicative (Index (s + 2) → K)) (v : Index (s + 3) → K) :
    ((radicalHom K h2 s z).val : Mat K (s + 3)) *ᵥ v =
      poleShear K h2 (s + 2) z.toAdd v := radicalElement_apply K h2 s z.toAdd v

theorem parameter_zero_of_central (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : Multiplicative (Index (s + 2) → K))
    (hz : radicalHom K h2 s z ∈ Subgroup.center (elementaryRootGroup K (s + 3))) :
    z.toAdd = 0 := by
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K (s + 2) h2
    (radicalHom K h2 s z)).mp hz
  let E := coordinateEquiv K h2 (s + 2)
  let v := E.symm (0, ((0 : Index (s + 2) → K), 1))
  have he : poleShear K h2 (s + 2) z.toAdd v = c • v := by
    rw [← radicalHom_apply K h2 s z, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hh := congrArg E he
  change coordinates K (s + 2) (poleShear K h2 (s + 2) z.toAdd v) = E (c • v) at hh
  rw [coordinates_poleShear, map_smul] at hh
  change transform (quadratic K (s + 2)) z.toAdd
      (E (E.symm (0, ((0 : Index (s + 2) → K), 1)))) =
    c • E (E.symm (0, ((0 : Index (s + 2) → K), 1))) at hh
  rw [LinearEquiv.apply_symm_apply] at hh
  have ht := congrArg (fun x : K × ((Index (s + 2) → K) × K) => x.2.1) hh
  change (0 : Index (s + 2) → K) + (1 : K) • z.toAdd = c • (0 : Index (s + 2) → K) at ht
  simpa only [zero_add, one_smul, smul_zero] using ht

def projectiveRadicalHom (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Multiplicative (Index (s + 2) → K) →* elementaryProjective K (s + 3) :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3)))).comp
    (radicalHom K h2 s)

theorem projectiveRadicalHom_injective (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Function.Injective (projectiveRadicalHom K h2 s) := by
  apply (MonoidHom.ker_eq_bot_iff (projectiveRadicalHom K h2 s)).mp
  apply bot_unique
  intro z hz
  have hc : radicalHom K h2 s z ∈ Subgroup.center (elementaryRootGroup K (s + 3)) :=
    (QuotientGroup.eq_one_iff _).mp hz
  have he := parameter_zero_of_central K h2 s z hc
  exact Subgroup.mem_bot.mpr (congrArg Multiplicative.ofAdd he)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalHom
