import SymmetricSubgroupAsymptotics.Non2LiftBound
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {G B : Type} [Group G] [Group B]
    (pi : G →* B) (A : Rep.{0} (ZMod 2) B)
    (e : Multiplicative A ≃* pi.ker) (r : B → G)
    (hr : ∀ b,pi (r b)=b)
    (hconj : ∀ b v,(e (Multiplicative.ofAdd (A.ρ b v)) : G)=
      r b*(e (Multiplicative.ofAdd v) : G)*(r b)⁻¹)
 def ofSection : OriginalKernelModuleChart pi A where
  equiv := e
  conjugate q v := by
    let k : pi.ker := ⟨q*(r (pi q))⁻¹,by
      change pi (q*(r (pi q))⁻¹)=1
      rw [map_mul,map_inv,hr,mul_inv_cancel]⟩
    let x := e.symm k
    have hx : (e x : G)=q*(r (pi q))⁻¹ := congrArg Subtype.val (e.apply_symm_apply k)
    have hq : q=(e x : G)*r (pi q) := by rw [hx]; group
    have hc : (e x : G)*(e (Multiplicative.ofAdd (A.ρ (pi q) v)) : G)*(e x : G)⁻¹=
        (e (Multiplicative.ofAdd (A.ρ (pi q) v)) : G) := by
      have h : x*Multiplicative.ofAdd (A.ρ (pi q) v)*x⁻¹=
          Multiplicative.ofAdd (A.ρ (pi q) v) := by simp [mul_comm]
      have he := congrArg (fun z : Multiplicative A => (e z : G)) h
      simpa only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv] using he
    calc
      (e (Multiplicative.ofAdd (A.ρ (pi q) v)) : G) =
          (e x : G)*(e (Multiplicative.ofAdd (A.ρ (pi q) v)) : G)*(e x : G)⁻¹ := hc.symm
      _ = (e x : G)*(r (pi q)*(e (Multiplicative.ofAdd v) : G)*(r (pi q))⁻¹)*(e x : G)⁻¹ := by rw [hconj]
      _ = q*(e (Multiplicative.ofAdd v) : G)*q⁻¹ := by
        conv_rhs => rw [hq]
        group
end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
