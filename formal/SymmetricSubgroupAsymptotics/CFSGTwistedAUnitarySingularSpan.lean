import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankTwoSingularSpan
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySubspaceCompression

/-! Literal singular vectors span every natural unitary space of
positive rank. Even vector dimensions use their coordinate axes;
odd dimensions use the checked three-space trace base and hyperbolic
middle induction. The smallest fields are retained throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices

private theorem axis_singular_of_rev_ne (q : CFSG.PrimePower) (r : ℕ) (i : Fin (r+1))
    (hi : i.rev ≠ i) : unitaryNaturalPair q r (Pi.single i 1) (Pi.single i 1) = 0 := by
  rw [unitaryNaturalPair_basis]
  simp only [Pi.single_apply,if_neg hi,mul_zero]

theorem unitary_singular_span_eq_top_of_odd (q : CFSG.PrimePower) (r : ℕ) (hr : Odd r) :
    Submodule.span (q.Extension 2)
      {v : Fin (r+1) → q.Extension 2 | unitaryNaturalPair q r v v = 0} = ⊤ := by
  classical
  let S := Submodule.span (q.Extension 2)
    {v : Fin (r+1) → q.Extension 2 | unitaryNaturalPair q r v v = 0}
  have haxis (i : Fin (r+1)) : Pi.single i (1 : q.Extension 2) ∈ S := by
    apply Submodule.subset_span
    apply axis_singular_of_rev_ne
    intro he
    have hi := congrArg Fin.val he
    rw [Fin.val_rev] at hi
    have hib := i.isLt
    obtain ⟨k,hk⟩ := hr
    omega
  apply top_unique
  intro v _
  have he : v = ∑ i : Fin (r+1),v i • Pi.single i (1 : q.Extension 2) := by
    funext j
    simp [Finset.sum_apply,Pi.single_apply]
  rw [he]
  exact S.sum_mem (fun i _ => S.smul_mem _ (haxis i))

theorem unitary_evenRank_singular_span_eq_top (q : CFSG.PrimePower) (n : ℕ) :
    Submodule.span (q.Extension 2)
      {v : Fin (2*n+2+1) → q.Extension 2 | unitaryNaturalPair q (2*n+2) v v = 0} = ⊤ := by
  induction n with
  | zero => exact unitary_rankTwo_singular_span_eq_top q
  | succ n ih =>
    classical
    let s := 2*n+2
    change Submodule.span (q.Extension 2)
      {v : Fin (s+3) → q.Extension 2 | unitaryNaturalPair q (s+2) v v = 0} = ⊤
    let S := Submodule.span (q.Extension 2)
      {v : Fin (s+3) → q.Extension 2 | unitaryNaturalPair q (s+2) v v = 0}
    have hmid : ∀ u : Fin (s+1) → q.Extension 2,unitaryMiddleVector q s u ∈ S := by
      have hle : Submodule.span (q.Extension 2)
          {u : Fin (s+1) → q.Extension 2 | unitaryNaturalPair q s u u = 0} ≤
            S.comap (unitaryMiddleVector q s) := by
        apply Submodule.span_le.mpr
        intro u hu
        apply Submodule.subset_span
        change unitaryNaturalPair q (s+2) (unitaryMiddleVector q s u) (unitaryMiddleVector q s u) = 0
        change unitaryNaturalPair q s u u = 0 at hu
        rw [unitaryMiddleVector_pair,hu,neg_zero]
      rw [ih] at hle
      exact fun u => hle trivial
    have hfirst : Pi.single (0 : Fin (s+3)) (1 : q.Extension 2) ∈ S := by
      apply Submodule.subset_span
      apply axis_singular_of_rev_ne
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.rev_zero,Fin.val_last,Fin.val_zero] at hh
      omega
    have hlast : Pi.single (Fin.last (s+2)) (1 : q.Extension 2) ∈ S := by
      apply Submodule.subset_span
      apply axis_singular_of_rev_ne
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.rev_last,Fin.val_last,Fin.val_zero] at hh
      omega
    apply top_unique
    intro v _
    let w := v - v (Fin.last (s+2)) • Pi.single (Fin.last (s+2)) (1 : q.Extension 2)
    have hw : w (Fin.last (s+2)) = 0 := by simp [w]
    have hdecomp := unitary_vector_decomposition q s w hw
    have hwm : w ∈ S := by
      rw [hdecomp]
      exact S.add_mem (S.smul_mem _ hfirst) (hmid _)
    have hv : v = w + v (Fin.last (s+2)) • Pi.single (Fin.last (s+2)) (1 : q.Extension 2) :=
      (sub_add_cancel _ _).symm
    rw [hv]
    exact S.add_mem hwm (S.smul_mem _ hlast)

theorem unitary_singular_span_eq_top (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) :
    Submodule.span (q.Extension 2)
      {v : Fin (r+1) → q.Extension 2 | unitaryNaturalPair q r v v = 0} = ⊤ := by
  rcases Nat.even_or_odd r with he | ho
  · obtain ⟨k,hk⟩ := he
    have hkpos : 1 ≤ k := by omega
    obtain ⟨n,rfl⟩ : ∃ n : ℕ,r=2*n+2 := ⟨k-1,by omega⟩
    exact unitary_evenRank_singular_span_eq_top q n
  · exact unitary_singular_span_eq_top_of_odd q r ho

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
