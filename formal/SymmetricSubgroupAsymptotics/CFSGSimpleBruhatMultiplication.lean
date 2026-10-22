import SymmetricSubgroupAsymptotics.CFSGWeylWordBruhatCover

/-! The local Bruhat multiplication step from a genuine complement
factorization, a uniform positive/negative root dichotomy, and the
rank-one nonzero Gauss factor. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGSimpleBruhatMultiplication
open CFSGWeylWordBruhatCover
variable {G K : Type*} [Group G] [Zero K]

theorem left_simple_cell (B U T V : Subgroup G) (s n b : G)
    (up low : K→G) (hUB : U≤B) (hTB : T≤B)
    (hfactor : ∃v∈V,∃a : K,∃t∈T,b=v*up a*t)
    (hV : ∀v∈V,s*v*s⁻¹∈B)
    (hT : ∀t∈T,n⁻¹*t*n∈T)
    (hroot : (∀a : K,n⁻¹*up a*n∈U) ∨ (∀a : K,n⁻¹*low a*n∈U))
    (hzero : up 0=1)
    (hGauss : ∀a : K,a≠0→∃c∈B,∃d : K,s*up a=c*low d) :
    DoubleCell B (s*n) (s*b*n) ∨ DoubleCell B n (s*b*n) := by
  obtain ⟨v,hv,a,t,ht,he⟩ := hfactor
  have hleft : s*v*s⁻¹∈B := hV v hv
  have hright : n⁻¹*t*n∈B := hTB (hT t ht)
  rcases hroot with hpos|hneg
  · left
    refine ⟨s*v*s⁻¹,hleft,(n⁻¹*up a*n)*(n⁻¹*t*n),
      B.mul_mem (hUB (hpos a)) hright,?_⟩
    rw [he]
    group
  · by_cases ha : a=0
    · left
      refine ⟨s*v*s⁻¹,hleft,n⁻¹*t*n,hright,?_⟩
      rw [he,ha,hzero]
      group
    · right
      obtain ⟨c,hc,d,hg⟩ := hGauss a ha
      refine ⟨(s*v*s⁻¹)*c,B.mul_mem hleft hc,
        (n⁻¹*low d*n)*(n⁻¹*t*n),B.mul_mem (hUB (hneg d)) hright,?_⟩
      calc
        s*b*n=(s*v*s⁻¹)*(s*up a)*t*n := by rw [he];group
        _=((s*v*s⁻¹)*c)*n*((n⁻¹*low d*n)*(n⁻¹*t*n)) := by rw [hg];group

end SymmetricSubgroupAsymptotics.CFSGSimpleBruhatMultiplication
