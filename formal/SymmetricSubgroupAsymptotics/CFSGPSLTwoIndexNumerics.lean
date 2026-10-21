import SymmetricSubgroupAsymptotics.CFSGPSLTwoPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGPSLTwoLeastIndexOrder
import SymmetricSubgroupAsymptotics.CFSGPSLTwoOuterBound
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds

/-! The two literal simple-index assertions for PSL2 over every finite
field of cardinality at least four. The small fields four and five use
the same faithful coset/order argument, without an A5 identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
open CFSGPSLTwoRootCoordinates PrimitiveSocleRawStructure
variable {F : Type} [Field F] [Finite F] [IsSimpleGroup (PSL (F:=F))]

theorem proper_index_ge_four (hq : 4≤Nat.card F)
    (H : Subgroup (PSL (F:=F))) (hH : H≠⊤) : 4≤H.index := by
  have hcore : H.normalCore=⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore H.normalCore_normal with h|h
    · exact h
    · exact (hH (top_le_iff.mp (h ▸ H.normalCore_le))).elim
  let f : PSL (F:=F)→*Equiv.Perm (PSL (F:=F) ⧸ H) :=
    MulAction.toPermHom _ _
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    exact (Subgroup.normalCore_eq_ker H).symm.trans hcore
  have hc : Nat.card (PSL (F:=F))≤H.index.factorial := by
    simpa only [Nat.card_perm,←H.index_eq_card] using Nat.card_le_card_of_injective f hf
  by_contra hs
  have hsmall : H.index.factorial≤6 := by
    have hh := Nat.factorial_le (by omega : H.index≤3)
    norm_num at hh ⊢
    exact hh
  have hlo : 60≤Nat.card F*(Nat.card F-1)*(Nat.card F+1) := by
    have h1 : 3≤Nat.card F-1 := by omega
    have h2 : 5≤Nat.card F+1 := by omega
    have hh := Nat.mul_le_mul (Nat.mul_le_mul hq h1) h2
    norm_num at hh
    exact hh
  have horder := twice_projective_card_ge_classical_order (F:=F)
  omega

theorem leastProperIndex_ge_four (hq : 4≤Nat.card F) (ell : ℕ)
    (hell : LeastProperIndex (PSL (F:=F)) ell) : 4≤ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  exact proper_index_ge_four hq H hH

theorem outer_card_le_three_logb_leastProperIndex (hq : 4≤Nat.card F) (ell : ℕ)
    (hell : LeastProperIndex (PSL (F:=F)) ell) :
    (Nat.card (Outer (PSL (F:=F))) : ℝ)≤3*Real.logb 2 ell := by
  have he4 : 4≤ell := leastProperIndex_ge_four hq ell hell
  have hepos : (0 : ℝ)<(ell : ℝ) := by exact_mod_cast (by omega : 0<ell)
  have hqpos : (0 : ℝ)<(Nat.card F : ℝ) := by exact_mod_cast (by omega : 0<Nat.card F)
  have hqle : (Nat.card F : ℝ)≤2*(ell : ℝ) := by
    exact_mod_cast field_card_le_twice_leastProperIndex ell hell
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) hqpos hqle
  rw [Real.logb_mul (by norm_num : (2 : ℝ)≠0) (ne_of_gt hepos),
    Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] at hlog
  have hlog4 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (by norm_num : (0 : ℝ)<(2 : ℝ)^2)
    (show (2 : ℝ)^2≤(ell : ℝ) by exact_mod_cast he4)
  have hfour : Real.logb 2 (4 : ℝ)=2 := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)]
    norm_num
  simp only [show (2 : ℝ)^2=4 by norm_num,hfour] at hlog4
  have hfield := CFSGFiniteFieldAutomorphisms.card_ringAut_le_logb F
  have hout : (Nat.card (Outer (PSL (F:=F))) : ℝ)≤2*(Nat.card (F ≃+* F) : ℝ) := by
    exact_mod_cast (CFSGPSLTwoOuterBound.outer_card_le (F:=F))
  linarith

theorem simpleIndexBounds (hq : 4≤Nat.card F) (ell : ℕ)
    (hell : LeastProperIndex (PSL (F:=F)) ell) :
    ell^2<Nat.card (PSL (F:=F)) ∧
      (Nat.card (Outer (PSL (F:=F))) : ℝ)≤3*Real.logb 2 ell :=
  ⟨leastProperIndex_square_lt_card hq ell hell,
    outer_card_le_three_logb_leastProperIndex hq ell hell⟩

end SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
