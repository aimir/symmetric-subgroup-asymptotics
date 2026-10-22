import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2ProjectiveFactors

/-! Actual determinant-zero matrix rays are exactly PG1×PG1. Existence
uses the proved nonzero outer factorization; uniqueness uses actual
range/transpose-range. This is symbolic over every field, not a census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

abbrev SingularMatrixLines := {L : Submodule K (Matrix (Fin 2) (Fin 2) K) //
  Module.finrank K L = 1 ∧ ∀ A ∈ L, Matrix.det A = 0}

theorem determinant_zero_on_span (A : Matrix (Fin 2) (Fin 2) K) (hA : Matrix.det A = 0) :
    ∀ B ∈ Submodule.span K {A}, Matrix.det B = 0 := by
  intro B hB
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hB
  rw [Matrix.det_smul, hA, mul_zero]

def segreLine (pq : RulingParameters K × RulingParameters K) : SingularMatrixLines K :=
  ⟨Submodule.span K {columnMap K pq.1.rep pq.2.rep},
    finrank_span_singleton (outer_nonzero K _ _ pq.1.rep_nonzero pq.2.rep_nonzero),
    determinant_zero_on_span K _ (columnPlane_det_zero K _ _ ⟨pq.2.rep, rfl⟩)⟩

theorem segreLine_injective : Function.Injective (segreLine K) := by
  intro p q he
  apply segrePoint_pair_injective K
  apply Projectivization.submodule_injective
  exact congrArg Subtype.val he

theorem segreLine_surjective : Function.Surjective (segreLine K) := by
  intro L
  have hne : L.val ≠ ⊥ := by
    intro he
    have hh := congrArg (fun W : Submodule K (Matrix (Fin 2) (Fin 2) K) => Module.finrank K W) he
    change Module.finrank K L.val = Module.finrank K (⊥ : Submodule K (Matrix (Fin 2) (Fin 2) K)) at hh
    rw [L.property.1, finrank_bot] at hh
    omega
  obtain ⟨A, hAL, hA⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u, v, hu, hv, hfac⟩ := exists_nonzero_outer_factors K A hA (L.property.2 A hAL)
  let p : RulingParameters K := Projectivization.mk K u hu
  let q : RulingParameters K := Projectivization.mk K v hv
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K u hu
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  have hpu : p.rep = a • u := ha.symm
  have hqv : q.rep = b • v := hb.symm
  have hcanon : (a * b) • A = columnMap K p.rep q.rep := by
    ext i j
    change ((a : K) * (b : K)) * A i j = p.rep i * q.rep j
    rw [hpu, hqv, hfac]
    change ((a : K) * (b : K)) * (u i * v j) = ((a : K) * u i) * ((b : K) * v j)
    ring
  have hspan : Submodule.span K {A} = Submodule.span K {columnMap K p.rep q.rep} :=
    Submodule.span_singleton_eq_span_singleton.mpr ⟨a * b, hcanon⟩
  have hL : Submodule.span K {A} = L.val := Submodule.eq_of_le_of_finrank_le
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hAL)
    (by rw [L.property.1, finrank_span_singleton hA])
  refine ⟨(p, q), ?_⟩
  apply Subtype.ext
  exact hspan.symm.trans hL

def segreLineEquiv : RulingParameters K × RulingParameters K ≃ SingularMatrixLines K :=
  Equiv.ofBijective (segreLine K) ⟨segreLine_injective K, segreLine_surjective K⟩

theorem singularMatrixLine_card [Finite K] : Nat.card (SingularMatrixLines K) = (Nat.card K + 1) ^ 2 := by
  rw [Nat.card_congr (segreLineEquiv K).symm, Nat.card_prod, rulingParameter_card]
  ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
