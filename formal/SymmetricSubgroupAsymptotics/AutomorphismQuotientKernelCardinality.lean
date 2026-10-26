import SymmetricSubgroupAsymptotics.PrimeFrattiniGenerators
import Mathlib.Algebra.Group.End

/-! Actual automorphisms acting trivially on a quotient are determined
by the displacements of a SAME generating tuple. Each displacement is
an actual element of the original quotient kernel. Specializing to the
proved Frattini generating tuple gives the genuine |Phi|^r bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AutomorphismQuotientKernelCardinality

variable {N Q : Type*} [Group N] [Group Q] [Finite N]

theorem card_le_kernel_pow_of_generating_tuple
    {ι : Type*} [Fintype ι] (π : N →* Q) (g : ι → N)
    (hgen : Subgroup.closure (Set.range g)=⊤)
    (A : Subgroup (MulAut N)) (htrivial : ∀ (a : A) (n : N), π (a.val n)=π n) :
    Nat.card A≤(Nat.card π.ker)^(Fintype.card ι) := by
  letI : Finite (MulAut N) := Finite.of_injective
    (fun a : MulAut N => (a : N → N)) DFunLike.coe_injective
  let f : A → (ι → π.ker) := fun a i =>
    ⟨a.val (g i)*(g i)⁻¹,by
      change π (a.val (g i)*(g i)⁻¹)=1
      rw [π.map_mul,π.map_inv,htrivial,mul_inv_cancel]⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply MulEquiv.ext
    intro n
    have hmaps : a.val.toMonoidHom=b.val.toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense hgen
      rintro x ⟨i,rfl⟩
      have hh := congrArg (fun z : π.ker => z.val) (congrFun he i)
      exact mul_right_cancel hh
    exact DFunLike.congr_fun hmaps n
  calc
    Nat.card A≤Nat.card (ι → π.ker) := Nat.card_le_card_of_injective f hf
    _=(Nat.card π.ker)^(Fintype.card ι) := by rw [Nat.card_fun,Nat.card_eq_fintype_card (α:=ι)]

theorem card_le_frattini_pow_primeRank (p : ℕ) [Fact p.Prime]
    (hN : IsPGroup p N) (A : Subgroup (MulAut N))
    (htrivial : ∀ (a : A) (n : N),
      primeAbelianizationGroupMap p N (a.val n)=primeAbelianizationGroupMap p N n) :
    Nat.card A≤(Nat.card (frattini N))^
      Module.finrank (ZMod p) (PrimeCharacters p N) := by
  obtain ⟨g,hg⟩ := exists_primeFrattini_generating_tuple p hN
  have hh := card_le_kernel_pow_of_generating_tuple (primeAbelianizationGroupMap p N)
    g hg A htrivial
  simpa only [primeAbelianizationGroupMap_ker p N hN,Fintype.card_fin] using hh

end SymmetricSubgroupAsymptotics.AutomorphismQuotientKernelCardinality
