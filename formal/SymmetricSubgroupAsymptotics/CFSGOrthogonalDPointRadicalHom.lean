import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleRootWords
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryCenter
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! The whole split-D hyperbolic point radical, retained in the literal
elementary group and its literal central quotient. Actual root words
realize every parameter; natural-vector action proves the group law. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalHom

open CFSGOrthogonalDSerreMatrices CFSGSplitQuadraticPoleCoordinates
open CFSGSplitQuadraticPoleRootWords CFSGSplitQuadraticPoleRootAction
open CFSGQuadraticHyperbolicShear
variable (K : Type) [Field K]

private theorem element_ext (s : ℕ) (g h : elementaryRootGroup K (s + 3))
    (he : ∀ v : Index (s + 3) → K,
      (g.val : Mat K (s + 3)) *ᵥ v = (h.val : Mat K (s + 3)) *ᵥ v) : g = h := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h := congrFun (he (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

def radicalElement (s : ℕ) (z : Index (s + 2) → K) : elementaryRootGroup K (s + 3) :=
  Classical.choose (poleShear_has_element K (s + 2) (by omega) z)

theorem radicalElement_apply (s : ℕ) (z : Index (s + 2) → K)
    (v : Index (s + 3) → K) :
    ((radicalElement K s z).val : Mat K (s + 3)) *ᵥ v = poleShear K (s + 2) z v :=
  Classical.choose_spec (poleShear_has_element K (s + 2) (by omega) z) v

def radicalHom (s : ℕ) :
    Multiplicative (Index (s + 2) → K) →* elementaryRootGroup K (s + 3) where
  toFun z := radicalElement K s z.toAdd
  map_one' := by
    apply element_ext K s
    intro v
    change ((radicalElement K s 0).val : Mat K (s + 3)) *ᵥ v =
      (1 : Mat K (s + 3)) *ᵥ v
    rw [radicalElement_apply, poleShear_zero_apply, Matrix.one_mulVec]
  map_mul' z t := by
    apply element_ext K s
    intro v
    change ((radicalElement K s (z.toAdd + t.toAdd)).val : Mat K (s + 3)) *ᵥ v =
      (((radicalElement K s z.toAdd).val : Mat K (s + 3)) *
        ((radicalElement K s t.toAdd).val : Mat K (s + 3))) *ᵥ v
    rw [← Matrix.mulVec_mulVec, radicalElement_apply, radicalElement_apply,
      radicalElement_apply, poleShear_add_apply]

theorem radicalHom_apply (s : ℕ) (z : Multiplicative (Index (s + 2) → K))
    (v : Index (s + 3) → K) :
    ((radicalHom K s z).val : Mat K (s + 3)) *ᵥ v =
      poleShear K (s + 2) z.toAdd v := radicalElement_apply K s z.toAdd v

theorem parameter_zero_of_central (s : ℕ)
    (z : Multiplicative (Index (s + 2) → K))
    (hz : radicalHom K s z ∈ Subgroup.center (elementaryRootGroup K (s + 3))) :
    z.toAdd = 0 := by
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K (s + 1)
    (radicalHom K s z)).mp hz
  have he := congrArg (fun A : Mat K (s + 3) =>
    coordinates K (s + 2) (A *ᵥ (Pi.single (Sum.inr 0) 1))) hc
  dsimp only at he
  rw [radicalHom_apply, coordinates_poleShear, coordinates_negative_axis] at he
  have ht := congrArg (fun x : K × ((Index (s + 2) → K) × K) => x.2.1) he
  change (0 : Index (s + 2) → K) + (1 : K) • z.toAdd = _ at ht
  have hz0 : z.toAdd = 0 := by
    funext i
    have hi := congrFun ht i
    cases i <;> simpa [Matrix.smul_mulVec, Matrix.one_mulVec, coordinates,
      CFSGOrthogonalDIndexTailCoordinates.tailIndex, Function.comp_def,
      Pi.single_apply] using hi
  exact hz0

def projectiveRadicalHom (s : ℕ) :
    Multiplicative (Index (s + 2) → K) →* elementaryProjective K (s + 3) :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3)))).comp
    (radicalHom K s)

theorem projectiveRadicalHom_injective (s : ℕ) :
    Function.Injective (projectiveRadicalHom K s) := by
  apply (MonoidHom.ker_eq_bot_iff (projectiveRadicalHom K s)).mp
  apply bot_unique
  intro z hz
  have hc : radicalHom K s z ∈ Subgroup.center (elementaryRootGroup K (s + 3)) :=
    (QuotientGroup.eq_one_iff _).mp hz
  have he := parameter_zero_of_central K s z hc
  exact Subgroup.mem_bot.mpr (congrArg Multiplicative.ofAdd he)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalHom
