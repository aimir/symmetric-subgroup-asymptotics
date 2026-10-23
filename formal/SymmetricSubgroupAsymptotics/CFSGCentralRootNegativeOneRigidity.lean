import SymmetricSubgroupAsymptotics.CFSGRootParameterAutomorphism
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements

/-! A normalized positive parameter-one element forces its opposite
negative parameter-one element, provided a genuine rank-one intertwiner
constraint is available. Central p-element separation transports the
original quotient relation back to the actual source word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralRootNegativeOneRigidity
open CFSGRootParameterAutomorphism CFSGCentralKernelPElements
variable {K J G : Type*} [Field K] [Group J] [Group G]
    {p : ℕ} [Fact p.Prime]

theorem negative_one_fixed
    (pi : J→*G) (P : Sylow p J)
    (hP : Function.Injective (pi.comp (P:Subgroup J).subtype))
    (hker : pi.ker≤Subgroup.center J)
    (X Y : Multiplicative K→*J)
    (hY : Function.Injective (pi.comp Y))
    (hpX : ∀t,∃k:ℕ,X t^(p^k)=1) (hpY : ∀t,∃k:ℕ,Y t^(p^k)=1)
    (hweyl : (X (Multiplicative.ofAdd 1)*Y (Multiplicative.ofAdd (-1))*X (Multiplicative.ofAdd 1))*
        X (Multiplicative.ofAdd 1)*
      (X (Multiplicative.ofAdd 1)*Y (Multiplicative.ofAdd (-1))*X (Multiplicative.ofAdd 1))⁻¹=
        Y (Multiplicative.ofAdd (-1)))
    (hconstraint : ∀b:K,b≠0→
      (X (Multiplicative.ofAdd 1)*Y (Multiplicative.ofAdd b)*X (Multiplicative.ofAdd 1))*
          X (Multiplicative.ofAdd 1)=
        Y (Multiplicative.ofAdd b)*
          (X (Multiplicative.ofAdd 1)*Y (Multiplicative.ofAdd b)*X (Multiplicative.ofAdd 1))→b= -1)
    (f : MulAut G) (hfY : (pi.comp Y).range.map f.toMonoidHom=(pi.comp Y).range)
    (hfX : f (pi (X (Multiplicative.ofAdd 1)))=pi (X (Multiplicative.ofAdd 1))) :
    f (pi (Y (Multiplicative.ofAdd (-1))))=pi (Y (Multiplicative.ofAdd (-1))) := by
  let B := parameterAut (pi.comp Y) hY f hfY
  let b : K := B (-1)
  have hb0 : b≠0 := by
    intro hb
    have hh : B (-1)=B 0 := hb.trans (map_zero B).symm
    exact (neg_ne_zero.mpr (one_ne_zero: (1:K)≠0)) (B.injective hh)
  have hFb : f (pi (Y (Multiplicative.ofAdd (-1))))=pi (Y (Multiplicative.ofAdd b)) :=
    (parameterAut_apply (pi.comp Y) hY f hfY (-1)).symm
  let w0 := X (Multiplicative.ofAdd 1)*Y (Multiplicative.ofAdd (-1))*X (Multiplicative.ofAdd 1)
  let w := X (Multiplicative.ofAdd 1)*Y (Multiplicative.ofAdd b)*X (Multiplicative.ofAdd 1)
  have hw : pi w=f (pi w0) := by
    simp only [w,w0,map_mul,hfX,hFb]
  have hrel0 : pi w0*pi (X (Multiplicative.ofAdd 1))*(pi w0)⁻¹=
      pi (Y (Multiplicative.ofAdd (-1))) := by
    simpa only [w0,map_mul,map_inv] using congrArg pi hweyl
  have hrel := congrArg f hrel0
  simp only [map_mul,map_inv] at hrel
  rw [←hw,hfX,hFb] at hrel
  have hproj : pi (w*X (Multiplicative.ofAdd 1)*w⁻¹)=pi (Y (Multiplicative.ofAdd b)) := by
    simpa only [map_mul,map_inv] using hrel
  have hx : ∃k:ℕ,(w*X (Multiplicative.ofAdd 1)*w⁻¹)^(p^k)=1 := by
    obtain ⟨k,hk⟩ := hpX (Multiplicative.ofAdd 1)
    refine ⟨k,?_⟩
    simpa only [map_pow,map_one] using congrArg (MulAut.conj w) hk
  have heq := eq_of_p_elements pi P hP hker _ _ hx (hpY (Multiplicative.ofAdd b)) hproj
  have hinter : w*X (Multiplicative.ofAdd 1)=Y (Multiplicative.ofAdd b)*w := by
    have hh := congrArg (fun z:J=>z*w) heq
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  have hb := hconstraint b hb0 hinter
  simpa only [hb] using hFb

end SymmetricSubgroupAsymptotics.CFSGCentralRootNegativeOneRigidity
