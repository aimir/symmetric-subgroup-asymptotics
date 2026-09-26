import SymmetricSubgroupAsymptotics.LinearJointAnnihilator

/-! The full common kernel of a linear family on an actual parameter
subspace. One parameter dimension retains exactly one nonzero kernel;
two independent parameters force zero under the pair-kernel hypothesis.
No list of parameter vectors replaces the original subspace. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k L V U : Type*} [Field k]
    [AddCommGroup L] [Module k L] [FiniteDimensional k L]
    [AddCommGroup V] [Module k V]
    [AddCommGroup U] [Module k U]

theorem linearFamily_iInf_ker_eq_of_finrank_one
    (F : L →ₗ[k] (V →ₗ[k] U)) (P : Submodule k L)
    (l : L) (hl : l ∈ P) (hl0 : l ≠ 0) (hdim : Module.finrank k P = 1) :
    (⨅ a : P, (F (a : L)).ker) = (F l).ker := by
  have hle : Submodule.span k ({l} : Set L) ≤ P :=
    (Submodule.span_singleton_le_iff_mem l P).mpr hl
  have hspan : Submodule.span k ({l} : Set L) = P :=
    Submodule.eq_of_le_of_finrank_eq hle
      ((finrank_span_singleton (K := k) hl0).trans hdim.symm)
  apply le_antisymm
  · exact iInf_le _ (⟨l, hl⟩ : P)
  · intro v hv
    apply (Submodule.mem_iInf (fun a : P => (F (a : L)).ker)).mpr
    intro a
    change F (a : L) v = 0
    have ha : (a : L) ∈ Submodule.span k ({l} : Set L) := by
      rw [hspan]
      exact a.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
    rw [← hc, map_smul, LinearMap.smul_apply,
      show F l v = 0 from hv, smul_zero]

theorem linearFamily_iInf_ker_finrank_of_finrank_one
    [FiniteDimensional k V]
    (F : L →ₗ[k] (V →ₗ[k] U)) (P : Submodule k L) (r : ℕ)
    (hsingle : ∀ l : L, l ≠ 0 → Module.finrank k (F l).ker = r)
    (hdim : Module.finrank k P = 1) :
    Module.finrank k ↥(⨅ a : P, (F (a : L)).ker) = r := by
  have hP : P ≠ ⊥ := by
    intro hz
    rw [hz, finrank_bot] at hdim
    exact Nat.zero_ne_one hdim
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  rw [linearFamily_iInf_ker_eq_of_finrank_one F P l hl hl0 hdim]
  exact hsingle l hl0

theorem linearFamily_iInf_ker_eq_bot_of_two_le
    (F : L →ₗ[k] (V →ₗ[k] U)) (P : Submodule k L)
    (hpair : ∀ v : Fin 2 → L, LinearIndependent k v →
      (F (v 0)).ker ⊓ (F (v 1)).ker = ⊥)
    (hdim : 2 ≤ Module.finrank k P) :
    (⨅ a : P, (F (a : L)).ker) = ⊥ := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hdim
  have hi : LinearIndependent k (fun i : Fin 2 => (v i : L)) :=
    hv.map' P.subtype P.ker_subtype
  have hle : (⨅ a : P, (F (a : L)).ker) ≤
      (F (v 0 : L)).ker ⊓ (F (v 1 : L)).ker :=
    le_inf (iInf_le _ (v 0)) (iInf_le _ (v 1))
  exact le_antisymm (hle.trans (hpair _ hi).le) bot_le

end SymmetricSubgroupAsymptotics
