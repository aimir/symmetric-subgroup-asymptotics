import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalKlein

/-! The normal characteristic complement as a literal R→C homomorphism,
with its exact block map and actual odd-kernel centralization. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalRegularHom
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneAlternatingCentralizerCommutators (R regular top regular_injective)
open BinaryPlaneAlternatingCentralizerKleinLift (centralRegular beta alpha)
open BinaryPlaneWreathActualOddKernel
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

theorem exists_lift (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    ∃ l : R →* C, Function.Injective l ∧ l.range.Normal ∧
      (∀ r, top C (l r)=regular r) ∧
      ∀ r (o : oddKernel C), Commute (l r) (o : C) := by
  obtain ⟨s,hs,hn⟩ := BinaryPlaneAlternatingNormalKlein.exists_normal_section C e heven
  let l := (centralRegular C).subtype.comp (s.comp regular.rangeRestrict)
  have hrange : l.range=s.range.map (centralRegular C).subtype := by
    ext x
    constructor
    · rintro ⟨r,rfl⟩
      exact ⟨s (regular.rangeRestrict r),⟨regular.rangeRestrict r,rfl⟩,rfl⟩
    · rintro ⟨d,⟨p,rfl⟩,rfl⟩
      obtain ⟨r,rfl⟩ := regular.rangeRestrict_surjective p
      exact ⟨r,rfl⟩
  have ht : ∀ r, top C (l r)=regular r := by
    intro r
    exact congrArg Subtype.val (hs (regular.rangeRestrict r))
  refine ⟨l,?_,hrange.symm ▸ hn,ht,?_⟩
  · intro r t h
    apply regular_injective
    exact (ht r).symm.trans ((congrArg (top C) h).trans (ht t))
  · intro r o
    have ha : alpha C (l r)=1 := (s (regular.rangeRestrict r)).property.1
    have hh := congrArg (fun f : MulAut (oddKernel C) => (f o : C)) ha
    change l r*(o : C)*(l r)⁻¹=(o : C) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

/-- Normality supplies actual lift conjugation, without replacing the
normalizer by a pure top model. -/
theorem conjugation_lift (C : Subgroup Frame) (l : R →* C) [l.range.Normal]
    (g : C) (r : R) : ∃ s : R, g*l r*g⁻¹=l s := by
  have hh : g*l r*g⁻¹∈l.range := (inferInstance : l.range.Normal).conj_mem
    (l r) ⟨r,rfl⟩ g
  obtain ⟨s,hs⟩ := hh
  exact ⟨s,hs.symm⟩

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalRegularHom
