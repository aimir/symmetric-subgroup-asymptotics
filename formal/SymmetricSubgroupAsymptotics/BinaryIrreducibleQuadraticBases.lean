import SymmetricSubgroupAsymptotics.BinaryLinearQuadraticDichotomy
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual two-orbit bases for the binary identity T^2+T+I=0.
An invariant orbit plane has no eigenvector in its quotient, so a
vector outside that plane supplies a second disjoint orbit plane. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryIrreducibleQuadraticBases
open BinaryLinearQuadraticDichotomy

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem square_apply (hK : Nat.card K=2) (e : V ≃ₗ[K] V)
    (he : ∀v : V, e (e v)+e v+v=0) (v : V) : e (e v)=e v+v := by
  have hh : e (e v)+(e v+v)=0 := by simpa only [add_assoc] using he v
  exact (eq_neg_iff_add_eq_zero.mpr hh).trans (neg_eq_self hK (e v+v))

theorem pair_independent (hK : Nat.card K=2) (e : V ≃ₗ[K] V)
    (he : ∀v : V, e (e v)+e v+v=0) (v : V) (hv : v ≠ 0) :
    LinearIndependent K ![v,e v] := by
  apply (LinearIndependent.pair_iff' hv).mpr
  intro a ha
  rcases scalar_eq_zero_or_one hK a with h0 | h1
  · have hev : e v=0 := by simpa only [h0, zero_smul] using ha.symm
    exact hv (e.injective (hev.trans (map_zero e).symm))
  · have hfix : e v=v := by simpa only [h1, one_smul] using ha.symm
    have hh := square_apply hK e he v
    rw [hfix, hfix] at hh
    exact hv (add_left_cancel (by simpa only [add_zero] using hh.symm))

theorem four_independent_of_outside (hK : Nat.card K=2) (e : V ≃ₗ[K] V)
    (he : ∀v : V, e (e v)+e v+v=0) (v : V) (hv : v ≠ 0) (u : V)
    (hu : u ∉ Submodule.span K ({v,e v} : Set V)) :
    LinearIndependent K ![v,e v,u,e u] := by
  let P := Submodule.span K ({v,e v} : Set V)
  have hvP : v ∈ P := Submodule.subset_span (by simp)
  have hevP : e v ∈ P := Submodule.subset_span (by simp)
  have hP : ∀w : V, w ∈ P → e w ∈ P := by
    intro w hw
    obtain ⟨a,b,hw⟩ := Submodule.mem_span_pair.mp hw
    rw [←hw, map_add, map_smul, map_smul]
    exact P.add_mem (P.smul_mem a hevP)
      (P.smul_mem b (by rw [square_apply hK e he v]; exact P.add_mem hevP hvP))
  have hdouble (w : V) : w+w=0 := by
    calc
      w+w = -w+w := congrArg (fun z : V => z+w) (neg_eq_self hK w).symm
      _ = 0 := neg_add_cancel w
  have hsum : e (e u)+e u=u := by
    rw [square_apply hK e he u]
    calc
      e u+u+e u = (e u+e u)+u := by abel
      _ = u := by rw [hdouble, zero_add]
  have hnot : e u ∉ Submodule.span K ({v,e v,u} : Set V) := by
    intro hm
    obtain ⟨a,b,c,hc⟩ := Submodule.mem_span_triple.mp hm
    have hw : a • v+b • e v ∈ P := P.add_mem (P.smul_mem a hvP) (P.smul_mem b hevP)
    rcases scalar_eq_zero_or_one hK c with hc0 | hc1
    · have heu : e u ∈ P := by
        rw [←hc, hc0, zero_smul, add_zero]
        exact hw
      have hh := P.add_mem (hP (e u) heu) heu
      rw [hsum] at hh
      exact hu hh
    · have hh : e u+u ∈ P := by
        rw [←hc, hc1, one_smul, add_assoc, hdouble, add_zero]
        exact hw
      have hh' := hP (e u+u) hh
      rw [map_add, hsum] at hh'
      exact hu hh'
  have hpair := pair_independent hK e he v hv
  have hr2 : Set.range ![v,e v]=({v,e v} : Set V) := by
    simp only [Matrix.range_cons_cons_empty]
  have hr3 : Set.range ![v,e v,u]=({v,e v,u} : Set V) := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  have hthree : LinearIndependent K (Fin.snoc ![v,e v] u) :=
    linearIndependent_finSnoc.mpr ⟨hpair, by simpa only [hr2] using hu⟩
  have hs3 : Fin.snoc ![v,e v] u=![v,e v,u] := by ext i; fin_cases i <;> rfl
  rw [hs3] at hthree
  have hfour : LinearIndependent K (Fin.snoc ![v,e v,u] (e u)) :=
    linearIndependent_finSnoc.mpr ⟨hthree, by simpa only [hr3] using hnot⟩
  have hs4 : Fin.snoc ![v,e v,u] (e u)=![v,e v,u,e u] := by
    ext i; fin_cases i <;> rfl
  simpa only [hs4] using hfour

theorem exists_independent_four [FiniteDimensional K V]
    (hK : Nat.card K=2) (e : V ≃ₗ[K] V)
    (he : ∀v : V, e (e v)+e v+v=0) (hd : 2 < Module.finrank K V) :
    ∃v u : V, LinearIndependent K ![v,e v,u,e u] := by
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K)
    (by omega : 0 < Module.finrank K V)
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  have hpair := pair_independent hK e he v hv
  let P := Submodule.span K ({v,e v} : Set V)
  have hrange : Set.range ![v,e v]=({v,e v} : Set V) := by
    ext z
    constructor
    · rintro ⟨i,hi⟩
      fin_cases i
      · exact Or.inl hi.symm
      · exact Or.inr hi.symm
    · rintro (hz | hz)
      · exact ⟨0,hz.symm⟩
      · exact ⟨1,hz.symm⟩
  have hdim : Module.finrank K P=2 := by
    have hh := finrank_span_eq_card hpair
    rw [hrange,Fintype.card_fin] at hh
    exact hh
  have hproper : P ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hdim
    omega
  obtain ⟨u,hu⟩ : ∃u : V, u ∉ P := by
    by_contra hn
    exact hproper (Submodule.eq_top_iff'.mpr (by simpa only [not_exists, not_not] using hn))
  exact ⟨v,u,four_independent_of_outside hK e he v hv u hu⟩

theorem not_finrank_three [FiniteDimensional K V]
    (hK : Nat.card K=2) (e : V ≃ₗ[K] V)
    (he : ∀v : V, e (e v)+e v+v=0) : Module.finrank K V ≠ 3 := by
  intro hd
  obtain ⟨v,u,hvu⟩ := exists_independent_four hK e he (by omega)
  have hh := hvu.fintype_card_le_finrank
  simp only [Fintype.card_fin, hd] at hh
  omega

theorem exists_basis_pairs [FiniteDimensional K V]
    (hK : Nat.card K=2) (e : V ≃ₗ[K] V)
    (he : ∀v : V, e (e v)+e v+v=0) (hd : Module.finrank K V=4) :
    ∃b : Module.Basis (Fin 4) K V, e (b 0)=b 1 ∧ e (b 2)=b 3 := by
  obtain ⟨v,u,hvu⟩ := exists_independent_four hK e he (by omega)
  let b := basisOfLinearIndependentOfCardEqFinrank' ![v,e v,u,e u] hvu
    (by simpa only [Fintype.card_fin] using hd.symm)
  refine ⟨b, ?_, ?_⟩
  · simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank',
      Matrix.cons_val_zero,Matrix.cons_val_one]
  · simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank']
    rfl

end SymmetricSubgroupAsymptotics.BinaryIrreducibleQuadraticBases
