import SymmetricSubgroupAsymptotics.PrincipalRingCyclicSubmodules
import SymmetricSubgroupAsymptotics.RepresentationPolynomialGeneratorBound

/-! A cyclic coordinate action over a principal ideal ring supplies a
uniform bound for the original acting ring when every original submodule
is stable under that coordinate action. This includes polynomial actions
over a larger coefficient field realized by actual acting operators. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Polynomial

namespace SymmetricSubgroupAsymptotics
namespace ModuleGeneratedBy

variable {R A M N : Type} [Ring R] [CommRing A] [IsPrincipalIdealRing A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module A N]

theorem one_of_principal_coordinates (e : M ≃+ N)
    (hstable : ∀ (W : Submodule R M) (a : A) (x : M), x ∈ W →
      e.symm (a • e x) ∈ W)
    (hgen : ModuleGeneratedBy A N 1) (W : Submodule R M) :
    ModuleGeneratedBy R W 1 := by
  let WA : Submodule A N :=
    { carrier := {x | e.symm x ∈ W}
      zero_mem' := by simpa using W.zero_mem
      add_mem' := fun hx hy ↦ by simpa using W.add_mem hx hy
      smul_mem' := fun a x hx ↦ by
        simpa only [e.apply_symm_apply] using hstable W a (e.symm x) hx }
  obtain ⟨v, hv⟩ := uniform_one_of_principalIdealRing hgen WA
  let w : Fin 1 → W := fun i ↦ ⟨e.symm (v i).1, (v i).property⟩
  let P : Submodule R W := Submodule.span R (Set.range w)
  let S : Submodule R M := P.map W.subtype
  let Q : Submodule A WA :=
    { carrier := {x | e.symm x.1 ∈ S}
      zero_mem' := by simpa using S.zero_mem
      add_mem' := fun hx hy ↦ by simpa using S.add_mem hx hy
      smul_mem' := fun a x hx ↦ by
        simpa only [e.apply_symm_apply] using hstable S a (e.symm x.1) hx }
  have hvQ : Submodule.span A (Set.range v) ≤ Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨w i, Submodule.subset_span (Set.mem_range_self i), rfl⟩
  have hQ : Q = ⊤ := by
    rw [hv] at hvQ
    exact top_unique hvQ
  refine ⟨w, top_unique ?_⟩
  intro x _
  have hxA : e x.1 ∈ WA := by
    change e.symm (e x.1) ∈ W
    rw [e.symm_apply_apply]
    exact x.property
  have hxQ : (⟨e x.1, hxA⟩ : WA) ∈ Q := by
    rw [hQ]
    exact Submodule.mem_top
  have hxS : x.1 ∈ S := by
    change e.symm (e x.1) ∈ S at hxQ
    simpa only [e.symm_apply_apply] using hxQ
  obtain ⟨y, hy, hxy⟩ := hxS
  have heq : y = x := Subtype.ext hxy
  exact heq ▸ hy

end ModuleGeneratedBy

namespace ModuleGeneratedBy

variable {R K M V : Type} [Ring R] [Field K]
  [AddCommGroup M] [Module R M] [AddCommGroup V] [Module K V]

/-- A cyclic polynomial coordinate operator over any field suffices
provided both its scalars and its action preserve the original submodules. -/
theorem one_of_polynomial_coordinates (e : M ≃+ V) (T : Module.End K V)
    (hscalar : ∀ (W : Submodule R M) (a : K) (x : M), x ∈ W →
      e.symm (a • e x) ∈ W)
    (hoperator : ∀ (W : Submodule R M) (x : M), x ∈ W →
      e.symm (T (e x)) ∈ W)
    (v : Fin 1 → Module.AEval' T)
    (hv : Submodule.span K[X] (Set.range v) = ⊤)
    (W : Submodule R M) : ModuleGeneratedBy R W 1 := by
  let e' : M ≃+ Module.AEval' T := e.trans (Module.AEval'.of T).toAddEquiv
  apply one_of_principal_coordinates (A := K[X]) e' ?_ ⟨v, hv⟩ W
  intro S p x hx
  let P : Submodule K V :=
    { carrier := {y | e.symm y ∈ S}
      zero_mem' := by simpa using S.zero_mem
      add_mem' := fun hy hz ↦ by simpa using S.add_mem hy hz
      smul_mem' := fun a y hy ↦ by
        simpa only [e.apply_symm_apply] using hscalar S a (e.symm y) hy }
  have hPT : ∀ y, y ∈ P → T y ∈ P := by
    intro y hy
    simpa only [e.apply_symm_apply] using hoperator S (e.symm y) hy
  let Q := Module.AEval.mapSubmodule K V T ⟨P, hPT⟩
  have hxQ : Module.AEval'.of T (e x) ∈ Q := by
    apply (Module.AEval.mem_mapSubmodule_apply K V T).mpr
    change e.symm (e x) ∈ S
    simpa only [e.symm_apply_apply] using hx
  have hp := (Module.AEval.mem_mapSubmodule_apply K V T).mp (Q.smul_mem p hxQ)
  exact hp

end ModuleGeneratedBy
end SymmetricSubgroupAsymptotics

end
