import SymmetricSubgroupAsymptotics.CFSGFiniteHermitianNondegenerateComplement

/-! Nondegenerate Hermitian lines are isometric when every nonzero fixed
scalar is a norm. The line maps and their scaling are constructed here;
the norm-surjectivity input will be supplied by the actual quadratic
finite-field extension. No Witt extension theorem is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianLineIsometry
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem norm_ne_zero (C : Submodule K (I → K)) (hd : Module.finrank K C = 1)
    (hND : ∀ x ∈ C, (∀ y ∈ C, hermitianPair sigma H x y = 0) → x = 0)
    (x : C) (hx : x ≠ 0) : hermitianPair sigma H x.val x.val ≠ 0 := by
  intro hn
  apply hx
  apply Subtype.ext
  apply hND _ x.property
  intro y hy
  obtain ⟨a,ha⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp hd ⟨y,hy⟩
  have he := congrArg (fun z : C => z.val) ha
  change a • x.val = y at he
  rw [← he]
  have hh := hermitianPair_smul sigma H 1 a x.val x.val
  simpa only [one_smul,map_one,one_mul,hn,mul_zero] using hh

theorem exists_isometry (C D : Submodule K (I → K))
    (hC : Module.finrank K C = 1) (hD : Module.finrank K D = 1)
    (hCN : ∀ x ∈ C, (∀ y ∈ C, hermitianPair sigma H x y = 0) → x = 0)
    (hDN : ∀ x ∈ D, (∀ y ∈ D, hermitianPair sigma H x y = 0) → x = 0)
    (hfixed : ∀ x, sigma (hermitianPair sigma H x x) = hermitianPair sigma H x x)
    (hnorm : ∀ a : K, a ≠ 0 → sigma a = a → ∃ t : K, sigma t * t = a) :
    ∃ e : C ≃ₗ[K] D, ∀ x y : C,
      hermitianPair sigma H (e x).val (e y).val = hermitianPair sigma H x.val y.val := by
  obtain ⟨x,hx⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := C)).mp
    (by rw [hC]; exact Nat.zero_lt_one)
  let E : C ≃ₗ[K] D := LinearEquiv.ofFinrankEq C D (hC.trans hD.symm)
  have hex : E x ≠ 0 := fun h => hx (E.injective (h.trans (map_zero E).symm))
  let nC := hermitianPair sigma H x.val x.val
  let nD := hermitianPair sigma H (E x).val (E x).val
  have hnC : nC ≠ 0 := norm_ne_zero sigma H C hC hCN x hx
  have hnD : nD ≠ 0 := norm_ne_zero sigma H D hD hDN (E x) hex
  have hratio : sigma (nC / nD) = nC / nD := by
    rw [map_div₀,hfixed,hfixed]
  obtain ⟨t,htnorm⟩ := hnorm (nC / nD) (div_ne_zero hnC hnD) hratio
  have ht : t ≠ 0 := by
    intro hz
    have hh := htnorm
    rw [hz,map_zero,mul_zero] at hh
    exact (div_ne_zero hnC hnD) hh.symm
  let e : C ≃ₗ[K] D := E.trans (LinearEquiv.smulOfNeZero K D t ht)
  have henorm : hermitianPair sigma H (e x).val (e x).val = nC := by
    change hermitianPair sigma H (t • (E x).val) (t • (E x).val) = nC
    rw [hermitianPair_smul,htnorm]
    exact div_mul_cancel₀ nC hnD
  refine ⟨e,?_⟩
  intro y z
  obtain ⟨a,rfl⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp hC y
  obtain ⟨b,rfl⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp hC z
  simp only [map_smul]
  change hermitianPair sigma H (a • (e x).val) (b • (e x).val) =
    hermitianPair sigma H (a • x.val) (b • x.val)
  rw [hermitianPair_smul,hermitianPair_smul,henorm]

end SymmetricSubgroupAsymptotics.CFSGHermitianLineIsometry
