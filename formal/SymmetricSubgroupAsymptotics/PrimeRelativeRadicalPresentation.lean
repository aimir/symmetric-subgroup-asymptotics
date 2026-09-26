import SymmetricSubgroupAsymptotics.PrimeRelativeRadical
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The actual relative-character radical has its group-theoretic
presentation by all p-th powers in N and the mixed commutator [N,G].
The reverse inclusion uses characters of the literal elementary quotient,
not a declared quotient order, a generator-number input, or a p-group
hypothesis. Finite-generator reduction and finite certificate bindings are
separate from this generic equality. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement IsMulCommutative

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- All original p-th powers, together with the full original mixed commutator. -/
def primeRelativePowerCommutator : Subgroup G :=
  Subgroup.closure (Set.range (fun n : N => (n : G)^p)) ⊔ ⁅N,(⊤ : Subgroup G)⁆

theorem primeRelativePowerCommutator_le : primeRelativePowerCommutator p N ≤ N := by
  apply sup_le
  · apply (Subgroup.closure_le N).mpr
    rintro x ⟨n,rfl⟩
    exact N.pow_mem n.2 p
  · exact Subgroup.commutator_le_left N ⊤

theorem primeRelativePowerCommutator_pow_mem (n : N) :
    (n : G)^p ∈ primeRelativePowerCommutator p N := by
  apply (show Subgroup.closure (Set.range (fun n : N => (n : G)^p)) ≤
    primeRelativePowerCommutator p N from le_sup_left)
  exact Subgroup.subset_closure (Set.mem_range_self n)

theorem primeRelativePowerCommutator_commutator_le :
    ⁅N,(⊤ : Subgroup G)⁆ ≤ primeRelativePowerCommutator p N := le_sup_right

/-- Any conjugating ambient element is allowed: [S,G] ≤ [N,G] ≤ S. -/
instance primeRelativePowerCommutator_normal : (primeRelativePowerCommutator p N).Normal :=
  Subgroup.commutator_top_right_le_iff.mp
    ((Subgroup.commutator_mono (primeRelativePowerCommutator_le p N) le_rfl).trans
      (primeRelativePowerCommutator_commutator_le p N))

theorem pow_mem_primeRelativeRadical (n : N) : (n : G)^p ∈ primeRelativeRadical p N := by
  apply (coe_mem_primeRelativeRadical_iff p N (n^p)).mpr
  apply (mem_primeRelativeRadicalKernel_iff p N (n^p)).mpr
  intro χ
  have h := χ.1.map_nsmul p (Additive.ofMul n)
  change χ.1 (Additive.ofMul (n^p))=p • χ.1 (Additive.ofMul n) at h
  rw [h]
  exact ZModModule.char_nsmul_eq_zero p _

/-- Mixed commutators vanish because the character is invariant under all G. -/
theorem commutator_mem_primeRelativeRadical (n : N) (g : G) :
    ⁅(n : G),g⁆ ∈ primeRelativeRadical p N := by
  let m : N := ⟨g*(n : G)*g⁻¹,Subgroup.Normal.conj_mem inferInstance _ n.2 g⟩
  have hm : ((n*m⁻¹ : N) : G) ∈ primeRelativeRadical p N := by
    apply (coe_mem_primeRelativeRadical_iff p N (n*m⁻¹)).mpr
    apply (mem_primeRelativeRadicalKernel_iff p N (n*m⁻¹)).mpr
    intro χ
    have hinv : χ.1 (Additive.ofMul m)=χ.1 (Additive.ofMul n) := χ.2 g n
    simp only [ofMul_mul,ofMul_inv,map_add,map_neg,hinv,add_neg_cancel]
  have he : ((n*m⁻¹ : N) : G)=⁅(n : G),g⁆ := by
    change (n : G)*(g*(n : G)*g⁻¹)⁻¹=⁅(n : G),g⁆
    rw [commutatorElement_def]
    group
  exact he ▸ hm

theorem primeRelativePowerCommutator_le_radical :
    primeRelativePowerCommutator p N ≤ primeRelativeRadical p N := by
  apply sup_le
  · apply (Subgroup.closure_le (primeRelativeRadical p N)).mpr
    rintro x ⟨n,rfl⟩
    exact pow_mem_primeRelativeRadical p N n
  · apply Subgroup.commutator_le.mpr
    intro n hn g _
    exact commutator_mem_primeRelativeRadical p N ⟨n,hn⟩ g

/-- The literal quotient is commutative since its kernel contains [N,N]. -/
theorem primeRelativePowerQuotient_commutative :
    IsMulCommutative (N ⧸ (primeRelativePowerCommutator p N).subgroupOf N) := by
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  intro n hn
  change (n : G) ∈ primeRelativePowerCommutator p N
  have hm : (n : G) ∈ (commutator N).map N.subtype := ⟨n,hn,rfl⟩
  rw [N.map_subtype_commutator] at hm
  exact primeRelativePowerCommutator_commutator_le p N
    ((Subgroup.commutator_mono le_rfl le_top) hm)

theorem primeRelativePowerQuotient_pow_eq_one
    (x : N ⧸ (primeRelativePowerCommutator p N).subgroupOf N) : x^p=1 := by
  obtain ⟨n,rfl⟩ := QuotientGroup.mk'_surjective
    ((primeRelativePowerCommutator p N).subgroupOf N) x
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact primeRelativePowerCommutator_pow_mem p N n

/-- Conjugation is literally trivial on this original quotient of N. -/
theorem primeRelativePowerQuotient_conjugate (g : G) (n : N) :
    QuotientGroup.mk' ((primeRelativePowerCommutator p N).subgroupOf N)
      (⟨g*(n : G)*g⁻¹,Subgroup.Normal.conj_mem inferInstance _ n.2 g⟩ : N) =
      QuotientGroup.mk' ((primeRelativePowerCommutator p N).subgroupOf N) n := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (g*(n : G)*g⁻¹)/(n : G) ∈ primeRelativePowerCommutator p N
  have hm : ⁅g,(n : G)⁆ ∈ ⁅(⊤ : Subgroup G),N⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top g) n.2
  rw [Subgroup.commutator_comm] at hm
  have hs := primeRelativePowerCommutator_commutator_le p N hm
  simpa only [commutatorElement_def,div_eq_mul_inv] using hs

private theorem primeRelative_character_separation
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (q : Additive N →+ V)
    (hq : ∀ (g : G) (n : N),
      q (Additive.ofMul
        (⟨g*(n : G)*g⁻¹,Subgroup.Normal.conj_mem inferInstance _ n.2 g⟩ : N)) =
          q (Additive.ofMul n))
    (n : N) (hn : ∀ χ : primeRelativeCharacters p N,
      χ.1 (Additive.ofMul n)=0) : q (Additive.ofMul n)=0 := by
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod p) _).mp
  intro ell
  exact hn ⟨ell.toAddMonoidHom.comp q,by
    intro g m
    exact congrArg ell (hq g m)⟩

/-- Scalar duals of the actual quotient separate its nontrivial elements.
Their pullbacks are precisely eligible full-ambient invariant characters. -/
theorem primeRelativeRadical_le_powerCommutator :
    primeRelativeRadical p N ≤ primeRelativePowerCommutator p N := by
  let D : Subgroup N := (primeRelativePowerCommutator p N).subgroupOf N
  letI : IsMulCommutative (N ⧸ D) := primeRelativePowerQuotient_commutative p N
  letI : Module (ZMod p) (Additive (N ⧸ D)) :=
    AddCommGroup.zmodModule (n := p) (fun x => by
      apply Additive.toMul.injective
      exact primeRelativePowerQuotient_pow_eq_one p N x.toMul)
  let q : N →* N ⧸ D := QuotientGroup.mk' D
  intro x hx
  obtain ⟨hxN,hχ⟩ := (mem_primeRelativeRadical_iff p N x).mp hx
  let n : N := ⟨x,hxN⟩
  have he : q n=1 := by
    change (Additive.ofMul (q n) : Additive (N ⧸ D))=0
    apply primeRelative_character_separation p N (V := Additive (N ⧸ D)) q.toAdditive
      (fun g m => congrArg Additive.ofMul (primeRelativePowerQuotient_conjugate p N g m)) n
    exact hχ
  exact (QuotientGroup.eq_one_iff (N := D) n).mp he

/-- The evaluation radical is exactly N^p[N,G], as literal ambient subgroups. -/
theorem primeRelativeRadical_eq_powerCommutator :
    primeRelativeRadical p N = primeRelativePowerCommutator p N :=
  le_antisymm (primeRelativeRadical_le_powerCommutator p N)
    (primeRelativePowerCommutator_le_radical p N)

end SymmetricSubgroupAsymptotics
