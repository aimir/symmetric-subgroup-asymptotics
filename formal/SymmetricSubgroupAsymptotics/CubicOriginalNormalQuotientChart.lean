import SymmetricSubgroupAsymptotics.OriginalKernelQuotientChart
import SymmetricSubgroupAsymptotics.CubicBinaryQuotientCoordinates
import Mathlib.Algebra.Module.ZMod

/-! Canonical inside-kernel normal quotients. The submodule is defined by
actual membership in the original normal subgroup; stability is proved from
normality. The existing original quotient chart and simultaneous Maschke
coordinates then apply without a normal-state census. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace CubicOriginalNormalQuotientChart

variable {G : Type} [Group G]
  (top : G →* CyclicThree) (htop : Function.Surjective top)
  (A : Rep (ZMod 2) CyclicThree) (E : OriginalKernelModuleChart top A)
  (N : Subgroup G) [N.Normal] (hN : N ≤ top.ker)

private def normalAddSubgroup : AddSubgroup A where
  carrier := {a | (E.equiv (Multiplicative.ofAdd a) : G) ∈ N}
  zero_mem' := by simpa using N.one_mem
  add_mem' := by
    intro a b ha hb
    change (E.equiv (Multiplicative.ofAdd (a+b)) : G) ∈ N
    rw [originalKernelChart_add]
    exact N.mul_mem ha hb
  neg_mem' := by
    intro a ha
    change (E.equiv (Multiplicative.ofAdd (-a)) : G) ∈ N
    simpa only [ofAdd_neg,map_inv,Subgroup.coe_inv] using N.inv_mem ha

/-- The retained normal subgroup as an actual original vector submodule. -/
def normalSubmodule : Submodule (ZMod 2) A :=
  (normalAddSubgroup top A E N).toZModSubmodule 2

omit [N.Normal] in
@[simp] theorem mem_normalSubmodule (a : A) :
    a ∈ normalSubmodule top A E N ↔
      (E.equiv (Multiplicative.ofAdd a) : G) ∈ N := Iff.rfl

include htop in
theorem normalSubmodule_stable (c : CyclicThree) :
    normalSubmodule top A E N ≤ (normalSubmodule top A E N).comap (A.ρ c) := by
  intro a ha
  obtain ⟨g,hg⟩ := htop c
  change (E.equiv (Multiplicative.ofAdd (A.ρ c a)) : G) ∈ N
  rw [← hg,E.conjugate]
  exact (inferInstance : N.Normal).conj_mem
    (E.equiv (Multiplicative.ofAdd a)) ha g

/-- The exact representation on the original quotient vector space. -/
def quotientModule : Rep (ZMod 2) CyclicThree :=
  OriginalKernelQuotientChart.quotientModule A (normalSubmodule top A E N)
    (normalSubmodule_stable top htop A E N)

/-- The original quotient-kernel chart, with denominator G/N retained. -/
def quotientChart : OriginalKernelModuleChart (QuotientGroup.lift N top hN)
    (quotientModule top htop A E N) :=
  OriginalKernelQuotientChart.quotientChart top A E (normalSubmodule top A E N)
    (normalSubmodule_stable top htop A E N) N hN (by
      intro a
      rfl)

/-- The actual module quotient map is equivariant and onto. -/
def projection : A.ρ.IntertwiningMap (quotientModule top htop A E N).ρ where
  toLinearMap := (normalSubmodule top A E N).mkQ
  isIntertwining' _ := rfl

def quotientCoordinates (D : CubicBinaryCoordinates A.ρ) :
    CubicBinaryCoordinates (quotientModule top htop A E N).ρ :=
  D.ofSurjective (projection top htop A E N)
    (normalSubmodule top A E N).mkQ_surjective

end CubicOriginalNormalQuotientChart
end SymmetricSubgroupAsymptotics
end
