import SymmetricSubgroupAsymptotics.OriginalKernelRetainedNonbinaryInterval
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! An actual binary quotient kills the whole fixed-free original binary
kernel when an odd cubic subgroup acts without invariants. The denominator
and the resulting factor map are unchanged original objects. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

variable {G B : Type} [Group G] [Group B]
  (pi : G →* B) (hpi : Function.Surjective pi)
  (A : Rep.{0} (ZMod 2) B) (E : OriginalKernelModuleChart pi A)
  (O : Subgroup B) [Finite O] [NeZero (Nat.card O : ZMod 2)]
  (hcubic : ∀ o : O,o^3=1)
  (hfixed : ∀ a : A,(∀ o : O,A.ρ (o : B) a=a) → a=0)

include E hcubic hfixed hpi in
 theorem binary_quotient_kills_kernel (N : Subgroup G) [N.Normal]
    (hQ : IsPGroup 2 (G ⧸ N)) : pi.ker≤N := by
  have hb : IsPGroup 2 (G ⧸ (pi.ker ⊔ N)) :=
    hQ.of_surjective (base pi N) (base_surjective pi N)
  have hle : O.comap pi≤N := by
    by_contra hnot
    exact E.retained_linear_nonbinary pi A N hpi O hcubic hfixed hnot hb
  apply le_trans _ hle
  intro g hg
  change pi g∈O
  rw [MonoidHom.mem_ker.mp hg]
  exact O.one_mem

include E hcubic hfixed hpi in
 theorem binary_quotient_factors_top (N : Subgroup G) [N.Normal]
    (hQ : IsPGroup 2 (G ⧸ N)) :
    ∃ f : B →* G ⧸ N,Function.Surjective f ∧ f.comp pi=QuotientGroup.mk' N :=
  CyclicSocleQuotientTools.exists_surjective_factor pi hpi
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (by
      rw [QuotientGroup.ker_mk']
      exact E.binary_quotient_kills_kernel pi hpi A O hcubic hfixed N hQ)

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
