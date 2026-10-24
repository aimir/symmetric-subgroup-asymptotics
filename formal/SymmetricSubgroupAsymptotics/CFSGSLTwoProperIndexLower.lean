import SymmetricSubgroupAsymptotics.CFSGPSLTwoGoodSylow
import SymmetricSubgroupAsymptotics.CFSGSquareScalarPermutationDegree

/-! The half-field proper-index lower bound for actual SL2, without a
simplicity hypothesis on SL2 or its central quotient. A nonzero upper
parameter normally generates: normality gives all square multiples,
their additive span is the whole field, and the opposite roots generate.
The actual torus then supplies the square-fixed-count degree bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSLTwoProperIndexLower

open CFSGTypeASLTwoWeyl CFSGTypeARootTorus CFSGSLTwoUpperRoots MulAction
variable {K : Type*} [Field K] [Finite K]

theorem normal_eq_top_of_upper_mem (N : Subgroup (SL2 (F := K))) [N.Normal]
    (a : K) (ha : a ≠ 0) (hNa : upper a ∈ N) : N = ⊤ := by
  let B := rootAddParameters N (by decide : (0 : Fin 2) ≠ 1)
  have hB : ∀ t : K, a * t ^ 2 ∈ B := by
    intro t
    by_cases ht : t = 0
    · simpa only [ht, zero_pow (by decide : 2 ≠ 0), mul_zero] using B.zero_mem
    · let u := Units.mk0 t ht
      have hn := (inferInstance : N.Normal).conj_mem (upper a) hNa
        (torus (by decide : (0 : Fin 2) ≠ 1) u)
      have he : torus (by decide : (0 : Fin 2) ≠ 1) u * upper a *
          (torus (by decide : (0 : Fin 2) ≠ 1) u)⁻¹ = upper (t ^ 2 * a) :=
        torus_conjugation (by decide : (0 : Fin 2) ≠ 1) u a
      rw [he] at hn
      change upper (a * t ^ 2) ∈ N
      simpa only [mul_comm] using hn
  have hBt : B = ⊤ := CFSGFiniteFieldSquareSpan.eq_top_of_scaled_squares B a ha hB
  have hu : upperRoot (F := K) ≤ N := by
    rintro g ⟨b, rfl⟩
    have hb : b.toAdd ∈ B := by rw [hBt]; trivial
    exact hb
  have hgen := CFSGPSLTwoGoodSylow.opposite_roots_generate (F := K)
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le N).2
  intro g hg
  rcases hg with hg | hg
  · exact hu hg
  · obtain ⟨h, hh, rfl⟩ := hg
    exact (inferInstance : N.Normal).conj_mem h (hu hh) (weyl (F := K))

theorem exists_moved_coset (H : Subgroup (SL2 (F := K))) (hH : H ≠ ⊤)
    (a : K) (ha : a ≠ 0) : ∃ x : SL2 (F := K) ⧸ H, upper a • x ≠ x := by
  by_contra hm
  have hk : upper a ∈ (MulAction.toPermHom (SL2 (F := K)) (SL2 (F := K) ⧸ H)).ker := by
    apply MonoidHom.mem_ker.mpr
    apply Equiv.Perm.ext
    intro x
    change upper a • x = x
    by_contra hx
    exact hm ⟨x, hx⟩
  rw [← H.normalCore_eq_ker] at hk
  have ht := normal_eq_top_of_upper_mem H.normalCore a ha hk
  exact hH (top_unique (ht ▸ H.normalCore_le))

theorem field_card_le_twice_proper_index (H : Subgroup (SL2 (F := K))) (hH : H ≠ ⊤) :
    Nat.card K ≤ 2 * H.index := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (SL2 (F := K) ⧸ H) := Fintype.ofFinite _
  letI : MulAction (Multiplicative K) (SL2 (F := K) ⧸ H) :=
    MulAction.compHom _ (upperHom (F := K))
  change Nat.card K ≤ 2 * Nat.card (SL2 (F := K) ⧸ H)
  apply CFSGSquareScalarPermutationDegree.card_le_twice_of_square_fixedBy
  · intro a c
    have he := Nat.card_congr
      (CFSGConjugateSubgroupDegree.fixedByConjugateEquiv (X := SL2 (F := K) ⧸ H)
        (upper (a : K)) (torus (by decide : (0 : Fin 2) ≠ 1) c))
    have hact : torus (by decide : (0 : Fin 2) ≠ 1) c * upper (a : K) *
        (torus (by decide : (0 : Fin 2) ≠ 1) c)⁻¹ = upper ((c : K) ^ 2 * (a : K)) :=
      torus_conjugation (by decide : (0 : Fin 2) ≠ 1) c (a : K)
    rw [hact] at he
    simpa only [MulAction.fixedBy, MulAction.compHom_smul_def, upperHom, mul_comm] using he.symm
  · intro a
    exact exists_moved_coset H hH a a.ne_zero

end SymmetricSubgroupAsymptotics.CFSGSLTwoProperIndexLower
