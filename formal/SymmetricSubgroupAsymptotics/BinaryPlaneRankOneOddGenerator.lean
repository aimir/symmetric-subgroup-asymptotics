import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelStructure
import SymmetricSubgroupAsymptotics.RankOneCubicSylowCentralizer

/-! A generator of the ACTUAL rank-one odd kernel is nontrivial on every
local plane. This claim is deliberately restricted to a single cubic line. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneRankOneOddGenerator
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel
open RankOneCubicSylowCentralizer (Cubic cubicGenerator)

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
  [Fintype I] [DecidableEq I]
  (C : Subgroup (W (R := R) (I := I)))
  (e : oddKernel C ≃* Cubic)

abbrev generator : oddKernel C := e.symm cubicGenerator

theorem generator_cube : generator C e ^ 3=1 := by
  apply e.injective
  rw [map_pow,MulEquiv.apply_symm_apply,map_one]
  decide +kernel

/-- Actual block transitivity propagates one nonzero odd projection; cyclic
rank one then forces this SPECIFIC generator to be nonzero everywhere. -/
theorem local_nontrivial
    (htrans : ∀ i j : I, ∃ h : C,
      (h : W (R := R) (I := I)).right • i=j) (i : I) :
    localLinear C i (generator C e)≠1 := by
  have hO : oddKernel C≠⊥ := by
    intro h
    have hgen : generator C e=1 := Subtype.ext (Subgroup.mem_bot.mp (h ▸
      (generator C e).property))
    have he := congrArg e hgen
    have hn : cubicGenerator≠1 := by decide +kernel
    exact hn (by simpa only [generator,MulEquiv.apply_symm_apply,map_one] using he)
  obtain ⟨g,hg⟩ := all_local_nontrivial C hO htrans i
  obtain ⟨n,hn⟩ := (by decide +kernel : ∀ z : Cubic,
    ∃ n : Fin 3, cubicGenerator^n.val=z) (e g)
  have hword : g=(generator C e)^n.val := by
    apply e.injective
    simpa only [generator,map_pow,MulEquiv.apply_symm_apply] using hn.symm
  intro hz
  apply hg
  rw [hword,map_pow,hz,one_pow]

/-- The local fixed-free hypotheses needed by the binary polynomial lemma
are proved from the original cubic line and actual block transporters. -/
theorem local_fixedFree
    (htrans : ∀ i j : I, ∃ h : C,
      (h : W (R := R) (I := I)).right • i=j)
    (i : I) (v : Plane)
    (hv : localLinear C i (generator C e) v=v) : v=0 :=
  BinaryPlaneNontrivialCubicFixedFree.fixedFree _
    (local_cubic C i (generator C e)) (local_nontrivial C e htrans i) v hv

end SymmetricSubgroupAsymptotics.BinaryPlaneRankOneOddGenerator
