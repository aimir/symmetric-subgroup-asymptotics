import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernel
import Mathlib.GroupTheory.PGroup

/-! Nonbinary actual images have a nonzero odd kernel; a transitive actual
block image makes all of its local projections nonzero. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernel
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
  [Fintype I] [DecidableEq I]

theorem sign_isPGroup (hR : IsPGroup 2 R) :
    IsPGroup 2 (Sign (R := R) (I := I)) := by
  obtain ⟨n,hn⟩ := hR.exists_card_eq
  apply IsPGroup.of_card (n := Module.finrank (ZMod 2)
    (TernaryPermutationWreathEmbedding.signs (R := R) (I := I)).toSubmodule + n)
  rw [SemidirectProduct.card,Nat.card_congr Multiplicative.toAdd,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hn,pow_add]

theorem oddKernel_ne_bot (C : Subgroup (W (R := R) (I := I)))
    (hR : IsPGroup 2 R) (hC : ¬ IsPGroup 2 C) : oddKernel C≠⊥ := by
  intro hbot
  have hinj : Function.Injective (signProjection C) :=
    (signProjection C).ker_eq_bot_iff.mp hbot
  exact hC ((sign_isPGroup (I := I) hR).of_injective (signProjection C) hinj)

/-- Conjugating by an actual block transporter conjugates the actual local
matrix. No pure block permutation or independent local element is used. -/
theorem localLinear_conjugate (C : Subgroup (W (R := R) (I := I)))
    (h : C) (g : oddKernel C) (i : I) :
    localLinear C ((h : W (R := R) (I := I)).right • i)
      ((MulAut.conjNormal h : MulAut (oddKernel C)) g) =
      (h : W (R := R) (I := I)).left ((h : W (R := R) (I := I)).right • i) *
        localLinear C i g *
      ((h : W (R := R) (I := I)).left ((h : W (R := R) (I := I)).right • i))⁻¹ := by
  change (((h : W (R := R) (I := I)) *
    ((g : C) : W (R := R) (I := I)) * (h : W (R := R) (I := I))⁻¹).left
      ((h : W (R := R) (I := I)).right • i)) = _
  simp only [PermutationalWreathProduct.mul_left,PermutationalWreathProduct.mul_right,
    PermutationalWreathProduct.inv_left,Pi.mul_apply,Pi.inv_apply,
    top_one C g,mul_one,inv_smul_smul,smul_inv_smul,localLinear]
  rfl

theorem all_local_nontrivial (C : Subgroup (W (R := R) (I := I)))
    (hO : oddKernel C≠⊥)
    (htrans : ∀ i j : I, ∃ h : C,
      (h : W (R := R) (I := I)).right • i=j) :
    ∀ j : I, ∃ g : oddKernel C, localLinear C j g≠1 := by
  letI : Nontrivial (oddKernel C) :=
    (oddKernel C).nontrivial_iff_ne_bot.mpr hO
  obtain ⟨g,hgone⟩ := exists_ne (1 : oddKernel C)
  have hsome : ∃ i : I, localLinear C i g≠1 := by
    by_contra hn
    push_neg at hn
    apply hgone
    apply Subtype.ext
    apply Subtype.ext
    apply PermutationalWreathProduct.ext
    · funext i
      exact hn i
    · exact top_one C g
  obtain ⟨i,hi⟩ := hsome
  intro j
  obtain ⟨h,hh⟩ := htrans i j
  refine ⟨(MulAut.conjNormal h : MulAut (oddKernel C)) g,?_⟩
  intro hz
  have hc := localLinear_conjugate C h g i
  rw [hh,hz] at hc
  have hc' := congrArg (fun x =>
    ((h : W (R := R) (I := I)).left j)⁻¹ * x *
      (h : W (R := R) (I := I)).left j) hc
  apply hi
  simpa [mul_assoc] using hc'.symm

end SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernel
