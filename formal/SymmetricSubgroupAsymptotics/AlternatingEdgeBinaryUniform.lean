import SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalProjectorHeads
import SymmetricSubgroupAsymptotics.CubicProjectorSchurCapacity
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryUniform
open AlternatingEdgeOriginalProjectorHeads (Top a beta)
open AlternatingEdgeBinaryProjectors
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem uniform : UniformSubrepresentationGeneratorBound beta 2 := by
  let H := Subgroup.zpowers a
  let c : H := ⟨a,Subgroup.mem_zpowers a⟩
  have ha : a^3=1 := by decide +kernel
  have hne : a≠1 := by decide +kernel
  have hcard : Nat.card H=3 := by rw [Nat.card_zpowers,orderOf_eq_prime ha hne]
  letI : NeZero (Nat.card H : ZMod 2) := ⟨by rw [hcard]; decide⟩
  let sigma : Representation (ZMod 2) H Vector := beta.comp H.subtype
  have hgen : ∀ h : H, ∃ n : ℕ, h=c^n := by
    intro h
    have hm : (h : Top) ∈ Submonoid.powers a := mem_powers_iff_mem_zpowers.mpr h.property
    obtain ⟨n,hn⟩ := hm
    exact ⟨n,Subtype.ext hn.symm⟩
  have hc : (sigma c)^3=1 := by
    change (beta a)^3=1
    rw [← map_pow,ha,map_one]
  have hmem : ∀ v : sigma.invariants, v.val ∈ fixed.range := by
    intro v
    refine ⟨v,?_⟩
    have hv : A v.val=v.val := v.property c
    change v.val+A v.val+A (A v.val)=v.val
    rw [hv,hv]
    have hz : v.val+v.val=0 := by
      rw [← two_smul (ZMod 2),show (2 : ZMod 2)=0 by decide,zero_smul]
    rw [hz,zero_add]
  let j := sigma.invariants.subtype.codRestrict fixed.range hmem
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : fixed.range => z.val) h)
  have hfixed : Module.finrank (ZMod 2) sigma.invariants≤2 :=
    (j.finrank_le_finrank_of_injective hj).trans fixed_rank_le_two
  have hg : RepresentationGeneratedBy sigma 2 :=
    CubicProjectorSchurCapacity.generatedBy_two sigma c hgen hc hfixed active_rank_le_four
  exact UniformSubrepresentationGeneratorBound.of_comp beta H.subtype
    (RepresentationGeneratedBy.uniform_of_invertible_order sigma hg)

end SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryUniform
