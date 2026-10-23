import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupKernel

/-! Opposed image recognition needs nontriviality only on the actual
simple witnesses extracted from strict upper overgroups. Subsequent
centrality needs injectivity only on a normalized generating root family,
not on the whole positive subgroup. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOpposedSimpleImageKernel
open CFSGOpposedSubgroupKernel
variable {G Q I:Type*} [Group G] [Group Q]

theorem normalizerPullback_le_upper_of_image_witness
    (f:G→*Q) (U V B:Subgroup G)
    (hB:B≤normalizerPullback f U)
    (hdisjoint:U.map f⊓V.map f=⊥)
    (hwitness:∀L:Subgroup G,B<L→∃n∈L,∃u∈U,
      n*u*n⁻¹∈V ∧ f u≠1) : normalizerPullback f U≤B := by
  by_cases he:normalizerPullback f U=B
  · exact he.le
  have hstrict:B<normalizerPullback f U:=lt_of_le_of_ne hB (Ne.symm he)
  obtain ⟨n,hn,u,hu,hv,hne⟩:=hwitness (normalizerPullback f U) hstrict
  have hnorm:f n∈Subgroup.normalizer (U.map f:Set Q):=hn
  have hpos:f (n*u*n⁻¹)∈U.map f := by
    rw [map_mul,map_mul,map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hnorm (f u)).mp ⟨u,hu,rfl⟩
  have hzero:f (n*u*n⁻¹)=1 := by
    apply Subgroup.mem_bot.mp
    rw [←hdisjoint]
    exact ⟨hpos,⟨n*u*n⁻¹,hv,rfl⟩⟩
  apply False.elim
  apply hne
  have h:=congrArg (fun z:Q=>(f n)⁻¹*z*f n) hzero
  simpa only [map_mul,map_inv,mul_assoc,inv_mul_cancel,mul_inv_cancel,
    inv_mul_cancel_left,mul_inv_cancel_left,one_mul,mul_one] using h

theorem kernel_le_upper_of_image_witness
    (f:G→*Q) (U V B:Subgroup G)
    (hB:B≤normalizerPullback f U)
    (hdisjoint:U.map f⊓V.map f=⊥)
    (hwitness:∀L:Subgroup G,B<L→∃n∈L,∃u∈U,
      n*u*n⁻¹∈V ∧ f u≠1) : f.ker≤B :=
  (kernel_le_normalizerPullback f U).trans
    (normalizerPullback_le_upper_of_image_witness f U V B hB hdisjoint hwitness)

theorem kernel_le_center_of_normalizing_injective_family
    (f:G→*Q) (X:I→Subgroup G) (D:Subgroup G)
    (hker:f.ker≤D)
    (hnorm:∀i,D≤Subgroup.normalizer (X i:Set G))
    (hinj:∀i,Set.InjOn f (X i:Set G))
    (hgen:(⨆i,X i)=⊤) : f.ker≤Subgroup.center G := by
  intro k hk
  have hcentralizes (i:I) : X i≤Subgroup.centralizer ({k}:Set G) := by
    intro t ht
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    have hxk:x=k:=Set.mem_singleton_iff.mp hx
    subst x
    have hc:k*t*k⁻¹∈X i :=
      (Subgroup.mem_normalizer_iff.mp (hnorm i (hker hk)) t).mp ht
    have he:f (k*t*k⁻¹)=f t := by
      rw [map_mul,map_mul,map_inv,show f k=1 from hk,one_mul,inv_one,mul_one]
    have hraw:=congrArg (fun z:G=>z*k) (hinj i hc ht he)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hraw
  have hall:(⊤:Subgroup G)≤Subgroup.centralizer ({k}:Set G) := by
    rw [←hgen]
    exact iSup_le hcentralizes
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (hall (Subgroup.mem_top g)) k
    (Set.mem_singleton k)).symm

end SymmetricSubgroupAsymptotics.CFSGOpposedSimpleImageKernel
