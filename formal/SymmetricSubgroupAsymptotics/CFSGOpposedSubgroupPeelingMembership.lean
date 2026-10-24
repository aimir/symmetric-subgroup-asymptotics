import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingChain

/-! A block belongs to a recursive residual if every actual inverse
suffix conjugate of that block is positive. The suffix is a group value,
not an action-class representative. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingMembership
open CFSGOpposedSubgroupPeeling CFSGOpposedSubgroupPeelingChain
variable {G : Type*} [Group G]

def inverseSuffix (w : ℕ → G) : ℕ → ℕ → G
  | 0,_ => 1
  | _+1,0 => 1
  | n+1,k+1 => inverseSuffix w n k * (w n)⁻¹

theorem le_residual_of_inverse_suffixes (U S : Subgroup G) (w : ℕ → G) (n : ℕ)
    (hpos : ∀ x∈S, ∀ k≤n,
      inverseSuffix w n k*x*(inverseSuffix w n k)⁻¹∈U) :
    S≤residual U w n := by
  induction n generalizing S with
  | zero =>
    intro x hx
    simpa only [inverseSuffix,one_mul,inv_one,mul_one] using hpos x hx 0 le_rfl
  | succ n ih =>
    have hnext : S.map (MulAut.conj ((w n)⁻¹)).toMonoidHom ≤ residual U w n := by
      apply ih
      rintro y ⟨x,hx,rfl⟩ k hk
      have h := hpos x hx (k+1) (Nat.succ_le_succ hk)
      change (inverseSuffix w n k*(w n)⁻¹)*x*
        (inverseSuffix w n k*(w n)⁻¹)⁻¹∈U at h
      change inverseSuffix w n k*((w n)⁻¹*x*((w n)⁻¹)⁻¹)*
        (inverseSuffix w n k)⁻¹∈U
      convert h using 1 <;> group
    intro x hx
    refine ⟨?_,?_⟩
    · simpa only [inverseSuffix,one_mul,inv_one,mul_one] using
        hpos x hx 0 (Nat.zero_le (n+1))
    · refine ⟨(w n)⁻¹*x*w n,?_,?_⟩
      · apply hnext
        refine ⟨x,hx,?_⟩
        change (w n)⁻¹*x*((w n)⁻¹)⁻¹=(w n)⁻¹*x*w n
        rw [inv_inv]
      · change w n*((w n)⁻¹*x*w n)*(w n)⁻¹=x
        group

end SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingMembership
