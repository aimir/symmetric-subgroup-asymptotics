import SymmetricSubgroupAsymptotics.BinaryPairNormalHead
import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport
import SymmetricSubgroupAsymptotics.BinaryWidthAsymptotics

/-! An unconditional cumulative Boolean-width bound for the relative
character head of every original normal subgroup of a faithful transitive
binary action. Each induction step retains the exact normal intersection
with the pair kernel and the exact image in the original pair top. No
normal-generation theorem, Tracey input, normal enumeration, or independent
kernel/top splitting is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

/-- All original normals are quantified in the induction statement. The
bound is sublinear by `binaryCumulativeWidth_normalized_tendsto_zero`, but
this theorem states the exact integer estimate at every degree, including
one. The action is the literal faithful permutation subgroup on X. -/
theorem transitiveBinary_normal_relativeHead_le_cumulative (k : ℕ) :
    ∀ {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
      [MulAction.IsPretransitive U X], IsPGroup 2 U → Nat.card X=2^k →
      ∀ (N : Subgroup U) [N.Normal],
        Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)≤binaryCumulativeWidth k := by
  induction k with
  | zero =>
    intro X _ U _ _ hcard N _
    have hc : Nat.card X=1 := by simpa only [pow_zero] using hcard
    letI : Subsingleton X := (Nat.card_eq_one_iff_unique.mp hc).1
    letI : Subsingleton U := inferInstance
    letI : Subsingleton N := inferInstance
    have hz (χ : primeRelativeCharacters 2 N) : χ=0 := by
      apply Subtype.ext
      ext n
      have hn : n=(0 : Additive N) := Subsingleton.elim _ _
      rw [hn]
      exact χ.1.map_zero
    letI : Subsingleton (primeRelativeCharacters 2 N) :=
      ⟨fun χ ψ => (hz χ).trans (hz ψ).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  | succ k ih =>
    intro X _ U _ hU hcard N _
    letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcard,pow_succ]
      have hp : 0<2^k := pow_pos (by decide) _
      omega)
    obtain ⟨D⟩ := transitiveBinaryPairCover_nonempty U hU
      (Classical.choice (inferInstance : Nonempty X))
    have hact : ∀ (u : U) (i : D.Points), u • i=D.frame.top u i := fun _ _ => rfl
    have hdegree : Nat.card D.Points=2^k := by
      have hd := D.degree_product
      rw [hcard,pow_succ] at hd
      omega
    have hkernel := D.frame.intersection_kernel_relativeHead_le_width
      hact N hU k hdegree D.base
    letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
    have htop := ih D.Top (D.top_isPGroup hU) hdegree
      (originalNormalRange D.frame.top N)
    have hchain := primeRelativeHead_chain_le
      (N⊓D.frame.top.ker) N 2 inf_le_left
    rw [primeRelativeHead_second_isomorphism 2 N D.frame.top.ker,
      primeRelativeHead_original_range 2 D.frame.top N] at hchain
    have hsum : binaryCumulativeWidth (k+1)=
        binaryCumulativeWidth k+k.choose (k/2) := by
      simp only [binaryCumulativeWidth,Finset.sum_range_succ]
    rw [hsum]
    exact hchain.trans ((Nat.add_le_add hkernel htop).trans_eq (Nat.add_comm _ _))

/-- The requested literal degree-2^k specialization. The normal remains
a subgroup of the original permutation group U, under all its conjugations. -/
theorem transitiveBinary_literal_normal_relativeHead_le_cumulative
    (k : ℕ) (U : Subgroup (Equiv.Perm (Fin (2^k))))
    [MulAction.IsPretransitive U (Fin (2^k))] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)≤binaryCumulativeWidth k :=
  transitiveBinary_normal_relativeHead_le_cumulative k U hU (Nat.card_fin _) N

end SymmetricSubgroupAsymptotics
