import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Lean.Elab.Tactic.Omega

/-!
# Equality in the maximal trivial-section dimension bound

Keep an endomorphism delta and literal ambient subspaces L <= M with
delta(M) <= L. If the actual quotient M/L has the full dimension of
ker(delta), rank-nullity forces the whole original kernel into M and
identifies L with delta(M). Consequently M is the full original preimage
of that image. No square-zero or image-equals-kernel assumption is needed
for these conclusions.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.MaximalTrivialSection

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]

/-- The quotient is formed inside the original M using the actual L,
not an abstract section with only a supplied dimension. -/
theorem eq_of_maximal_quotient_finrank
    (delta : V →ₗ[k] V) (M L : Submodule k V)
    (hLM : L≤M) (himage : M.map delta≤L)
    (hdim : Module.finrank k (M ⧸ L.comap M.subtype)=
      Module.finrank k delta.ker) :
    delta.ker≤M ∧ L=M.map delta ∧ M=(M.map delta).comap delta := by
  have hquot := (L.comap M.subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe hLM).finrank_eq] at hquot
  have hkerdim : Module.finrank k (delta.domRestrict M).ker =
      Module.finrank k ↥(M ⊓ delta.ker) := by
    rw [LinearMap.ker_domRestrict]
    have he := (M.equivSubtypeMap (delta.ker.comap M.subtype)).finrank_eq
    rw [Submodule.map_comap_subtype] at he
    exact he
  have hrank := (delta.domRestrict M).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict,hkerdim] at hrank
  have himagedim := Submodule.finrank_mono himage
  have hinterdim := Submodule.finrank_mono
    (show M ⊓ delta.ker≤delta.ker from inf_le_right)
  have hinter : M ⊓ delta.ker=delta.ker :=
    Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
  have hker : delta.ker≤M := hinter.symm.le.trans inf_le_left
  have hL : L=M.map delta :=
    (Submodule.eq_of_le_of_finrank_le himage (by omega)).symm
  refine ⟨hker,hL,?_⟩
  rw [Submodule.comap_map_eq,sup_eq_left.mpr hker]

/-- A square-zero endomorphism additionally places the actual L in the
original kernel, giving the literal nested subspaces needed by the
coordinate exact sequence. The ambient image need not equal the kernel. -/
theorem eq_of_maximal_quotient_finrank_of_square_zero
    (delta : V →ₗ[k] V) (M L : Submodule k V)
    (hLM : L≤M) (himage : M.map delta≤L)
    (hdim : Module.finrank k (M ⧸ L.comap M.subtype)=
      Module.finrank k delta.ker)
    (hsquare : delta.comp delta=0) :
    delta.ker≤M ∧ L=M.map delta ∧ L≤delta.ker ∧ M=L.comap delta := by
  obtain ⟨hker,hL,hpreimage⟩ :=
    eq_of_maximal_quotient_finrank delta M L hLM himage hdim
  refine ⟨hker,hL,?_,?_⟩
  · intro v hv
    rw [hL] at hv
    obtain ⟨m,_,rfl⟩ := hv
    change delta (delta m)=0
    exact LinearMap.congr_fun hsquare m
  · rw [hL]
    exact hpreimage

end SymmetricSubgroupAsymptotics.MaximalTrivialSection
