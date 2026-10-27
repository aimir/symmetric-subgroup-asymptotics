import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations
import Mathlib.Algebra.Lie.Subalgebra

/-! A finite source family containing the original Serre generators and
stable under their actual first root actions spans the WHOLE rational
Serre quotient. This conclusion needs neither integral saturation nor
realization faithfulness. It is useful for the odd-field scaled-coordinate
route, separately from the stronger integral-spanning route. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreFiniteRationalFirstActionSpan
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence

private def normalizer {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (S : Submodule ℚ L) : LieSubalgebra ℚ L where
  carrier := {x | ∀ y,y∈S→⁅x,y⁆∈S}
  zero_mem' := by intro y hy; simpa only [zero_lie] using S.zero_mem
  add_mem' := by
    intro x y hx hy z hz
    rw [add_lie]
    exact S.add_mem (hx z hz) (hy z hz)
  smul_mem' := by
    intro a x hx y hy
    rw [smul_lie]
    exact S.smul_mem a (hx y hy)
  lie_mem' := by
    intro x y hx hy z hz
    have he : ⁅⁅x,y⁆,z⁆=⁅x,⁅y,z⁆⁆-⁅y,⁅x,z⁆⁆ :=
      (eq_sub_iff_add_eq).mpr (leibniz_lie x y z).symm
    rw [he]
    exact S.sub_mem (hx _ (hy z hz)) (hy _ (hx z hz))

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    {J : Type*} (v : J→RationalLie A)

theorem span_eq_top
    (hgen : ∀ g,generator A g∈Submodule.span ℚ (Set.range v))
    (hfirst : ∀ neg i j,⁅rootVector A neg i,v j⁆∈Submodule.span ℚ (Set.range v)) :
    Submodule.span ℚ (Set.range v)=⊤ := by
  let S:=Submodule.span ℚ (Set.range v)
  let N:=normalizer S
  have hroot (neg : Bool) (i : Fin r) : rootVector A neg i∈N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨j,rfl⟩:=hy; exact hfirst neg i j
    | zero => rw [lie_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [lie_add]; exact S.add_mem hx hy
    | smul a x _ hx => rw [lie_smul]; exact S.smul_mem a hx
  have hgenerator (g : CartanMatrix.Generators (Fin r)) : generator A g∈N := by
    cases g with
    | E i => exact hroot false i
    | F i => exact hroot true i
    | H i =>
      rw [←generator_EF_same A i]
      exact N.lie_mem (hroot false i) (hroot true i)
  have hN : LieSubalgebra.lieSpan ℚ (RationalLie A) (Set.range (generator A))≤N := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro x ⟨g,rfl⟩
    exact hgenerator g
  rw [generator_lieSpan_eq_top A] at hN
  let T : LieSubalgebra ℚ (RationalLie A) :=
    { toSubmodule := S
      lie_mem' := by
        intro x y hx hy
        exact hN (show x∈(⊤ : LieSubalgebra ℚ (RationalLie A)) from trivial) y hy }
  have hT : LieSubalgebra.lieSpan ℚ (RationalLie A) (Set.range (generator A))≤T := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro x ⟨g,rfl⟩
    exact hgen g
  rw [generator_lieSpan_eq_top A] at hT
  apply top_unique
  intro x hx
  exact hT (show x∈(⊤ : LieSubalgebra ℚ (RationalLie A)) from trivial)

end SymmetricSubgroupAsymptotics.CFSGSerreFiniteRationalFirstActionSpan
