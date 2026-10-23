import SymmetricSubgroupAsymptotics.CFSGHermitianIsotropicExtension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A maximal singular space can be exchanged towards another one:
the new space gains a vector in the target and loses at most one
dimension of intersection with the old space. This is the concrete
gallery step needed to propagate local semilinear field components. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

def pairRightLinear (y : I → K) : (I → K) →ₗ[K] K where
  toFun x := hermitianPair sigma H y x
  map_add' x z := hermitianPair_add_right sigma H y x z
  map_smul' a x := by
    have hh := hermitianPair_smul sigma H 1 a y x
    simpa only [one_smul, map_one, one_mul, RingHom.id_apply, smul_eq_mul] using hh

theorem finrank_inf_ker_add_one_ge (S : Submodule K (I → K))
    (phi : (I → K) →ₗ[K] K) :
    Module.finrank K S ≤ Module.finrank K ↥(S ⊓ phi.ker) + 1 := by
  let f : S →ₗ[K] K := phi.comp S.subtype
  have hr : Module.finrank K f.range ≤ 1 := by
    simpa using (Submodule.finrank_le (R := K) f.range)
  have hn := f.finrank_range_add_finrank_ker
  have he : f.ker.map S.subtype = S ⊓ phi.ker := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.property, hv⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hd : Module.finrank K f.ker = Module.finrank K ↥(S ⊓ phi.ker) := by
    rw [← he]
    exact (Submodule.equivMapOfInjective S.subtype S.subtype_injective f.ker).finrank_eq
  omega

theorem maximal_exchange_towards (S T : Submodule K (I → K))
    (hS : MaximalIsotropic sigma H S) (hT : MaximalIsotropic sigma H T)
    (hswap : ∀ x y, hermitianPair sigma H x y = 0 ↔ hermitianPair sigma H y x = 0)
    (y : I → K) (hyT : y ∈ T) (hyS : y ∉ S) :
    ∃ M, MaximalIsotropic sigma H M ∧
      Module.finrank K S ≤ Module.finrank K ↥(S ⊓ M) + 1 ∧
      S ⊓ T < M ⊓ T := by
  let phi := pairRightLinear sigma H y
  let C := S ⊓ phi.ker
  have hCS : C ≤ S := inf_le_left
  have hyC : ∀ x ∈ C, hermitianPair sigma H y x = 0 := fun _ hx => hx.2
  have hCy : ∀ x ∈ C, hermitianPair sigma H x y = 0 := fun x hx => (hswap y x).mp (hyC x hx)
  have hC : Orthogonal sigma H C C := fun x hx z hz => hS.1 x (hCS hx) z (hCS hz)
  have hjoin : Orthogonal sigma H (C ⊔ K ∙ y) (C ⊔ K ∙ y) := by
    rw [orthogonal_sup_left_iff, orthogonal_sup_right_iff, orthogonal_sup_right_iff]
    exact ⟨⟨hC, (orthogonal_span_right_iff sigma H C y).mpr hCy⟩,
      (orthogonal_span_left_iff sigma H C y).mpr hyC,
      span_orthogonal_self sigma H y (hT.1 y hyT y hyT)⟩
  obtain ⟨M, hJM, hM⟩ := exists_maximalIsotropic_ge sigma H _ hjoin
  have hCM : C ≤ M := (show C ≤ C ⊔ K ∙ y from le_sup_left).trans hJM
  have hyM : y ∈ M := hJM ((show K ∙ y ≤ C ⊔ K ∙ y from le_sup_right)
    (Submodule.mem_span_singleton_self y))
  have hSTC : S ⊓ T ≤ C := by
    intro x hx
    exact ⟨hx.1, hT.1 y hyT x hx.2⟩
  have hle : S ⊓ T ≤ M ⊓ T := fun x hx => ⟨hCM (hSTC hx), hx.2⟩
  have hnle : ¬ M ⊓ T ≤ S ⊓ T := fun h => hyS (h ⟨hyM, hyT⟩).1
  refine ⟨M, hM, ?_, lt_of_le_not_ge hle hnle⟩
  have hc := finrank_inf_ker_add_one_ge S phi
  change Module.finrank K S ≤ Module.finrank K C + 1 at hc
  have hm := Submodule.finrank_mono (show C ≤ S ⊓ M from le_inf hCS hCM)
  omega

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
