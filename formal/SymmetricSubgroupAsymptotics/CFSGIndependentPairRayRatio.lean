import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Module

/-! Reciprocal ratios read from the SAME ray in two independent
original directions. Equality of spans supplies the scalar; independence
then proves the actual coefficient identity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIndependentPairRayRatio
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem product_eq_one (x y : V) (hxy : LinearIndependent K ![x,y]) (a b : K)
    (he : Submodule.span K {x+a•y}=Submodule.span K {y+b•x}) : a*b=1 := by
  have hm : y+b•x∈Submodule.span K {x+a•y} := he.symm ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
  have hz : (c-b)•x+(c*a-1)•y=0 := by
    calc
      _ = c•(x+a•y)-(y+b•x) := by module
      _ = 0 := sub_eq_zero.mpr hc
  obtain ⟨hcb,hca⟩ := LinearIndependent.pair_iff.mp hxy (c-b) (c*a-1) hz
  have hb : c=b := sub_eq_zero.mp hcb
  have ha : c*a=1 := sub_eq_zero.mp hca
  simpa only [hb,mul_comm] using ha

end SymmetricSubgroupAsymptotics.CFSGIndependentPairRayRatio
