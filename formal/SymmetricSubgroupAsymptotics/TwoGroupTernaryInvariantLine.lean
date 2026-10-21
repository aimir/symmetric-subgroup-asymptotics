import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-! A two-group acting linearly on a ternary three-dimensional space has
an actual invariant line. There are thirteen projective lines, so the
p-group fixed-point congruence proves this directly over F3. No splitting
field or irreducible-degree theorem is required. -/
set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.TwoGroupTernaryInvariantLine

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {P V : Type} [Group P] [AddCommGroup V] [Module (ZMod 3) V]
    [DistribMulAction P V] [SMulCommClass P (ZMod 3) V]

omit [DistribMulAction P V] [SMulCommClass P (ZMod 3) V] in
theorem projective_card (hdim : Module.finrank (ZMod 3) V=3) :
    Nat.card (Projectivization (ZMod 3) V)=13 := by
  rw [Projectivization.card_of_finrank (ZMod 3) V hdim]
  norm_num [Nat.card_zmod,Finset.sum_range_succ]

theorem fixed_projective (hP : IsPGroup 2 P)
    (hdim : Module.finrank (ZMod 3) V=3) :
    ∃ p : Projectivization (ZMod 3) V,∀ g : P,g • p=p := by
  obtain ⟨p,hp⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card
    (Projectivization (ZMod 3) V) (by rw [projective_card hdim]; decide)
  exact ⟨p,fun g => hp g⟩

theorem invariant_line (hP : IsPGroup 2 P)
    (hdim : Module.finrank (ZMod 3) V=3) :
    ∃ W : Submodule (ZMod 3) V,Module.finrank (ZMod 3) W=1 ∧
      ∀ (g : P) (v : V),v∈W → g • v∈W := by
  obtain ⟨p,hp⟩ := fixed_projective hP hdim
  have hrep (g : P) : g • p.rep∈p.submodule := by
    have he : Projectivization.mk (ZMod 3) (g • p.rep)
        ((smul_ne_zero_iff_ne g).mpr p.rep_nonzero)=p := by
      exact (Projectivization.smul_mk g p.rep_nonzero).symm.trans
        ((congrArg (fun q : Projectivization (ZMod 3) V => g • q) p.mk_rep).trans (hp g))
    have hs := congrArg Projectivization.submodule he
    change Submodule.span (ZMod 3) {g • p.rep}=p.submodule at hs
    rw [←hs]
    exact Submodule.mem_span_singleton_self _
  refine ⟨p.submodule,p.finrank_submodule,?_⟩
  intro g v hv
  have hv' : v∈Submodule.span (ZMod 3) {p.rep} := by
    simpa only [Projectivization.submodule_eq] using hv
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hv'
  rw [←ha,smul_comm g a p.rep]
  exact p.submodule.smul_mem a (hrep g)

end SymmetricSubgroupAsymptotics.TwoGroupTernaryInvariantLine
