import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleShearRelative
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCenter
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! The full twisted-D point radical is an actual relative-root group
hom. Original scalar-centre recognition and the literal opposite pole
prove its injection into the actual central quotient in every rank. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalHom

open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDFixedQuadraticAction CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDFixedPoleShear CFSGTwistedDFixedPoleShearRelative
open CFSGTwistedDFixedTailLinear CFSGTwistedDFixedPolePolar
open CFSGTwistedDRelativeCenter CFSGTwistedA2FixedField

def radicalElement (n : ℕ) (q : CFSG.PrimePower) (z : fixedSpace n q) :
    relativeRootGroup (n + 1) q :=
  Classical.choose (parameterHom_mem_relative_range n q z)

theorem radicalElement_linearHom (n : ℕ) (q : CFSG.PrimePower) (z : fixedSpace n q) :
    fixedLinearHom (n + 1) q (radicalElement n q z) =
      parameterHom n q (Multiplicative.ofAdd z) :=
  Classical.choose_spec (parameterHom_mem_relative_range n q z)

def radicalHom (n : ℕ) (q : CFSG.PrimePower) :
    Multiplicative (fixedSpace n q) →* relativeRootGroup (n + 1) q where
  toFun z := radicalElement n q z.toAdd
  map_one' := by
    apply fixedLinearHom_injective (n + 1) q
    change fixedLinearHom (n + 1) q (radicalElement n q 0) = fixedLinearHom (n + 1) q 1
    calc
      _ = parameterHom n q 1 := radicalElement_linearHom n q 0
      _ = 1 := (parameterHom n q).map_one
      _ = _ := (fixedLinearHom (n + 1) q).map_one.symm
  map_mul' z t := by
    apply fixedLinearHom_injective (n + 1) q
    change fixedLinearHom (n + 1) q (radicalElement n q (z.toAdd + t.toAdd)) =
      fixedLinearHom (n + 1) q (radicalElement n q z.toAdd * radicalElement n q t.toAdd)
    calc
      _ = parameterHom n q (z * t) := radicalElement_linearHom n q (z.toAdd + t.toAdd)
      _ = parameterHom n q z * parameterHom n q t := (parameterHom n q).map_mul z t
      _ = _ := by
        rw [map_mul, radicalElement_linearHom, radicalElement_linearHom]
        rfl

theorem radicalHom_linearHom (n : ℕ) (q : CFSG.PrimePower)
    (z : Multiplicative (fixedSpace n q)) :
    fixedLinearHom (n + 1) q (radicalHom n q z) = parameterHom n q z :=
  radicalElement_linearHom n q z.toAdd

theorem radicalHom_apply (n : ℕ) (q : CFSG.PrimePower)
    (z : Multiplicative (fixedSpace n q)) (v : fixedSpace (n + 1) q) :
    fixedLinearHom (n + 1) q (radicalHom n q z) v = poleShear n q z.toAdd v :=
  congrArg (fun A : fixedSpace (n + 1) q ≃ₗ[fixedField q] fixedSpace (n + 1) q => A v)
    (radicalHom_linearHom n q z)

theorem parameter_zero_of_central (n : ℕ) (q : CFSG.PrimePower)
    (z : Multiplicative (fixedSpace n q))
    (hz : radicalHom n q z ∈ Subgroup.center (relativeRootGroup (n + 1) q)) : z.toAdd = 0 := by
  obtain ⟨c, hc⟩ := (relativeRootGroup_center_iff_scalar (n + 1) q (radicalHom n q z)).mp hz
  let v := (poleEquiv n q).symm (0, ((0 : fixedSpace n q), 1))
  have hnv : negativeHead n q v = 1 := negativeHead_inv n q 0 1 0
  have hn : negativeHead n q (fixedLinearHom (n + 1) q (radicalHom n q z) v) = 1 := by
    rw [radicalHom_apply]
    have hh := congrArg (fun x : fixedField q × (fixedSpace n q × fixedField q) => x.2.2)
      (poleEquiv_poleShear n q z.toAdd v)
    change negativeHead n q (poleShear n q z.toAdd v) = negativeHead n q v at hh
    exact hh.trans hnv
  have hnvK : v.val (Sum.inr 0) = (1 : q.Extension 2) :=
    congrArg (fun a : fixedField q => (a : q.Extension 2)) hnv
  have hnK : (((radicalHom n q z).val : Mat (q.Extension 2) (n + 3)) *ᵥ v.val)
      (Sum.inr 0) = (1 : q.Extension 2) :=
    congrArg (fun a : fixedField q => (a : q.Extension 2)) hn
  have hc1 : c = 1 := by
    have hh := congrArg (fun A : Mat (q.Extension 2) (n + 3) => (A *ᵥ v.val) (Sum.inr 0)) hc
    dsimp only at hh
    rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hh
    change (((radicalHom n q z).val : Mat (q.Extension 2) (n + 3)) *ᵥ v.val)
      (Sum.inr 0) = c * v.val (Sum.inr 0) at hh
    rw [hnK, hnvK, mul_one] at hh
    exact hh.symm
  have hg : radicalHom n q z = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa only [hc1, one_smul] using hc
  have hp : parameterHom n q z = 1 := by
    rw [← radicalHom_linearHom, hg, map_one]
  have he := parameterHom_injective n q (hp.trans (parameterHom n q).map_one.symm)
  exact congrArg Multiplicative.toAdd he

def projectiveRadicalHom (n : ℕ) (q : CFSG.PrimePower) :
    Multiplicative (fixedSpace n q) →*
      (relativeRootGroup (n + 1) q ⧸ Subgroup.center (relativeRootGroup (n + 1) q)) :=
  (QuotientGroup.mk' (Subgroup.center (relativeRootGroup (n + 1) q))).comp (radicalHom n q)

theorem projectiveRadicalHom_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (projectiveRadicalHom n q) := by
  apply (MonoidHom.ker_eq_bot_iff (projectiveRadicalHom n q)).mp
  apply bot_unique
  intro z hz
  have hc : radicalHom n q z ∈ Subgroup.center (relativeRootGroup (n + 1) q) :=
    (QuotientGroup.eq_one_iff _).mp hz
  have he := parameter_zero_of_central n q z hc
  exact Subgroup.mem_bot.mpr (congrArg Multiplicative.ofAdd he)

end SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalHom
