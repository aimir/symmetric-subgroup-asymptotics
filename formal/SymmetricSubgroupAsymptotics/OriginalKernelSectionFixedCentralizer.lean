import SymmetricSubgroupAsymptotics.OriginalKernelSectionOddRestriction

/-! The fixed socle row has trivial intersection with the exact retained
translation kernel, for every original normal denominator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

variable {G B : Type} [Group G] [Group B]
  (pi : G →* B) (A : Rep.{0} (ZMod 2) B) (E : OriginalKernelModuleChart pi A)
  (N : Subgroup G) [N.Normal]

/-- The literal original preimage, then its literal image in G/N. It need
not be odd, and no averaging is performed over this subgroup. -/
def retainedOddSeparator (O : Subgroup B) : Subgroup (G ⧸ N) :=
  (O.comap pi).map (QuotientGroup.mk' N)

include E in
theorem retainedKernel_inf_centralizer_eq_bot
    (hpi : Function.Surjective pi)
    (O : Subgroup B) [Finite O] [NeZero (Nat.card O : ZMod 2)]
    (hfixed : ∀ a : A, (∀ o : O, A.ρ (o : B) a=a) → a=0) :
    (base pi N).ker ⊓ Subgroup.centralizer
      ((retainedOddSeparator pi N O) : Set (G ⧸ N)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  let q : (base pi N).ker := ⟨x,hx.1⟩
  obtain ⟨z,hz⟩ := (E.kernelEquiv pi A N).surjective q
  have hzero : z.toAdd=0 := by
    apply E.sectionFixedFreeOnOdd pi A N hpi O hfixed
    intro o
    obtain ⟨g,hg⟩ := hpi (o : B)
    let d : G ⧸ N := QuotientGroup.mk' N g
    have hd : d∈retainedOddSeparator pi N O :=
      ⟨g,by change pi g∈O; rw [hg]; exact o.property,rfl⟩
    have hcomm : d*x=x*d :=
      Subgroup.mem_centralizer_iff.mp hx.2 d hd
    have hbase : base pi N d=sectionTop pi N hpi (o : B) := by
      change QuotientGroup.mk' (pi.ker ⊔ N) g=sectionTop pi N hpi (o : B)
      rw [← hg,sectionTop_apply]
    apply Multiplicative.ofAdd.injective
    apply (E.kernelEquiv pi A N).injective
    apply Subtype.ext
    have hc := (E.quotientChart pi A N).conjugate d z.toAdd
    change (E.kernelEquiv pi A N
      (Multiplicative.ofAdd ((E.sectionRepresentation pi A N).ρ (base pi N d) z.toAdd)) :
        G ⧸ N) = d * (E.kernelEquiv pi A N z : G ⧸ N) * d⁻¹ at hc
    rw [hbase] at hc
    have hzcast : Multiplicative.ofAdd z.toAdd=z := rfl
    have hzc : (E.kernelEquiv pi A N (Multiplicative.ofAdd z.toAdd) : G ⧸ N)=
        (E.kernelEquiv pi A N z : G ⧸ N) :=
      congrArg (fun t => (E.kernelEquiv pi A N t : G ⧸ N)) hzcast
    have hzv : (E.kernelEquiv pi A N z : G ⧸ N)=x := congrArg Subtype.val hz
    exact hc.trans (by
      calc
        d*(E.kernelEquiv pi A N z : G ⧸ N)*d⁻¹=d*x*d⁻¹ :=
          congrArg (fun y => d*y*d⁻¹) hzv
        _=x := by rw [hcomm,mul_assoc,mul_inv_cancel,mul_one]
        _=(E.kernelEquiv pi A N (Multiplicative.ofAdd z.toAdd) : G ⧸ N) :=
          (hzc.trans hzv).symm)

  have hz1 : z=1 := by
    apply Multiplicative.toAdd.injective
    exact hzero
  have hq1 : q=1 := by
    rw [hz1,map_one] at hz
    exact hz.symm
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hq1)

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
