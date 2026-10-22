import SymmetricSubgroupAsymptotics.CFSGPolarPointFunctionals

/-! Opposite points are fixed once one singular space is pointwise
fixed and the other is stabilized, using only their actual nondegenerate
cross-pairing. No maximal-dimension bound or polar recognition is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem fixes_opposite_of_pairing_nondegenerate (B : LinearMap.BilinForm K V)
    (f : Points B≃Points B)
    (horth : ∀P Q,ZeroOn B (f P).val (f Q).val ↔ ZeroOn B P.val Q.val)
    (W Z : Subspaces B)
    (hnondeg : ∀v∈Z.val,(∀w∈W.val,B v w=0) → v=0)
    (hfix : ∀Q : Points B,Q.val≤W.val → f Q=Q)
    (hstable : ∀P : Points B,P.val≤Z.val → (f P).val≤Z.val) :
    ∀P : Points B,P.val≤Z.val → f P=P := by
  intro P hP
  obtain ⟨x,hx,hx0⟩ := point_nonzero B P
  obtain ⟨y,hy,hy0⟩ := point_nonzero B (f P)
  have hn : restrictedPairing B W x≠0 := by
    intro hz
    apply hx0
    exact hnondeg x (hP hx) (fun w hw=>LinearMap.congr_fun hz ⟨w,hw⟩)
  obtain ⟨c,hc,he⟩ := restrictedPairing_proportional B f horth W hfix P x y hx hy hx0 hy0 hn
  have hv : y-c•x∈Z.val := Z.val.sub_mem (hstable P hP hy) (Z.val.smul_mem c (hP hx))
  have hz : y-c•x=0 := hnondeg _ hv (by
    intro w hw
    have hh := LinearMap.congr_fun he ⟨w,hw⟩
    change B y w=c*B x w at hh
    simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,hh,sub_self])
  have hyP : y∈P.val := (sub_eq_zero.mp hz) ▸ P.val.smul_mem c hx
  exact (point_eq_of_common_nonzero B P (f P) y hyP hy hy0).symm

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
