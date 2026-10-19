import SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryProjectors
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryProjectors

def fixed : Module.End (ZMod 2) Vector := 1+A+A^2
private abbrev project6 (i : Fin 6) : Vector →ₗ[ZMod 2] ZMod 2 := LinearMap.proj i
private abbrev project2 (i : Fin 2) : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj i
private abbrev project4 (i : Fin 4) : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj i
private def fixedEncode : Vector →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  LinearMap.pi ![project6 0,project6 3]
private def fixedDecode : (Fin 2 → ZMod 2) →ₗ[ZMod 2] Vector :=
  LinearMap.pi ![project2 0,project2 0,project2 0,
    project2 1,project2 1,project2 1]
private def activeEncode : Vector →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  LinearMap.pi ![project6 0,project6 1,project6 3,project6 4]
private def activeDecode : (Fin 4 → ZMod 2) →ₗ[ZMod 2] Vector :=
  LinearMap.pi ![project4 0,project4 1,project4 0+project4 1,
    project4 2,project4 3,project4 2+project4 3]

private theorem range_rank_le_of_reconstruct {n : ℕ} (f : Module.End (ZMod 2) Vector)
    (encode : Vector →ₗ[ZMod 2] (Fin n → ZMod 2))
    (decode : (Fin n → ZMod 2) →ₗ[ZMod 2] Vector)
    (h : ∀ v, decode (encode (f v)) = f v) :
    Module.finrank (ZMod 2) f.range ≤ n := by
  let e := encode.comp f.range.subtype
  have hinj : Function.Injective e := by
    intro x y he
    change encode x.val = encode y.val at he
    have hx : decode (encode x.val) = x.val := by
      obtain ⟨v,hv⟩ := x.property
      rw [← hv]
      exact h v
    have hy : decode (encode y.val) = y.val := by
      obtain ⟨v,hv⟩ := y.property
      rw [← hv]
      exact h v
    exact Subtype.ext (hx.symm.trans ((congrArg decode he).trans hy))
  simpa using e.finrank_le_finrank_of_injective hinj

theorem fixed_rank_le_two : Module.finrank (ZMod 2) fixed.range ≤ 2 :=
  range_rank_le_of_reconstruct fixed fixedEncode fixedDecode (by decide +kernel)
theorem active_rank_le_four : Module.finrank (ZMod 2) active.range ≤ 4 :=
  range_rank_le_of_reconstruct active activeEncode activeDecode (by decide +kernel)

end SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryProjectors
