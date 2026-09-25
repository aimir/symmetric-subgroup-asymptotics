import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain

/-! A surjective map on an original ambient subgroup identifies its
literal ambient normal section with the actual target, via its exact
kernel. The isomorphism agrees with the original map on representatives. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A Q : Type*} [Group A] [Group Q]
variable (N B : Subgroup A) [N.Normal] [B.Normal]
variable (π : N→*Q) (hπ : Function.Surjective π) (hB : B=π.ker.map N.subtype)

include hB in
theorem normalSectionMap_kernel_eq : (normalChainMap B N).ker=π.ker := by
  ext n
  change normalChainMap B N n=1 ↔ π n=1
  constructor
  · intro h
    have hb : (n:A)∈B := (QuotientGroup.eq_one_iff (N:=B) (n:A)).mp
      (congrArg Subtype.val h)
    rw [hB] at hb
    obtain ⟨m,hm,he⟩ := hb
    have hmn : m=n := Subtype.ext he
    simpa only [hmn] using hm
  · intro h
    have hb : (n:A)∈B := by rw [hB]; exact ⟨n,h,rfl⟩
    exact Subtype.ext ((QuotientGroup.eq_one_iff (N:=B) (n:A)).mpr hb)

def normalSectionQuotientEquiv : normalChainQuotient B N ≃*Q :=
  (QuotientGroup.quotientKerEquivOfSurjective (normalChainMap B N)
    (normalChainMap_surjective B N)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (normalSectionMap_kernel_eq N B π hB)).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ))

theorem normalSectionQuotientEquiv_apply (n:N) :
    normalSectionQuotientEquiv N B π hπ hB (normalChainMap B N n)=π n := by
  let e := QuotientGroup.quotientKerEquivOfSurjective (normalChainMap B N)
    (normalChainMap_surjective B N)
  change QuotientGroup.quotientKerEquivOfSurjective π hπ
    (QuotientGroup.quotientMulEquivOfEq (normalSectionMap_kernel_eq N B π hB)
      (e.symm (e (QuotientGroup.mk n))))=π n
  rw [e.symm_apply_apply]
  rfl

end SymmetricSubgroupAsymptotics
