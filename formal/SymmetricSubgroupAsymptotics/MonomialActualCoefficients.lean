import SymmetricSubgroupAsymptotics.MonomialPolynomialOrbitGenerators

/-! Coordinate coefficients are extracted from the actual monomial
representation. Their nonzero and cocycle equations are proved from its
actual basis action, before any orbit restriction is constructed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MonomialActualCoefficients

variable {k G I : Type} [Field k] [Group G] [Fintype I] [DecidableEq I] [MulAction G I]
    (rho : Representation k G (I → k))
    (hdelta : ∀ g : G, ∀ i : I, ∃ u : kˣ,
      rho g (Pi.single i 1) = (u : k) • (Pi.single (g • i) 1 : I → k))

def coefficient (g : G) (i : I) : k :=
  rho g (Pi.single (g⁻¹ • i) 1) i

include hdelta in
omit [Fintype I] in
theorem coefficient_ne_zero (g : G) (i : I) : coefficient rho g i ≠ 0 := by
  obtain ⟨u,hu⟩ := hdelta g (g⁻¹ • i)
  have hi := congrFun hu i
  change coefficient rho g i = _ at hi
  simp only [smul_inv_smul,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one] at hi
  rw [hi]
  exact u.ne_zero

include hdelta in
/-- Every coordinate of every vector has its actual extracted coefficient. -/
theorem action_apply (g : G) (v : I → k) (i : I) :
    rho g v i = coefficient rho g i * v (g⁻¹ • i) := by
  have hv : (∑ x : I, v x • (Pi.single x 1 : I → k)) = v := by
    calc
      (∑ x : I, v x • (Pi.single x 1 : I → k)) = ∑ x : I, Pi.single x (v x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [←Pi.single_smul]
        simp only [smul_eq_mul,mul_one]
      _ = v := LinearMap.sum_single_apply (fun _ : I => k) v
  let a := g⁻¹ • i
  have hs : (∑ x : I, v x * rho g (Pi.single x 1) i) =
      v a * rho g (Pi.single a 1) i := by
    apply Finset.sum_eq_single a
    · intro x _ hxa
      obtain ⟨u,hu⟩ := hdelta g x
      have hix : i ≠ g • x := by
        intro h
        apply hxa
        have hh := congrArg (fun z => g⁻¹ • z) h
        have ha : a = x := by simpa only [inv_smul_smul] using hh
        exact ha.symm
      have hi := congrFun hu i
      simp only [Pi.smul_apply,Pi.single_eq_of_ne hix,smul_zero] at hi
      rw [hi,mul_zero]
    · intro h
      exact (h (Finset.mem_univ a)).elim
  calc
    rho g v i = rho g (∑ x : I, v x • (Pi.single x 1 : I → k)) i :=
      congrArg (fun w => rho g w i) hv.symm
    _ = ∑ x : I, v x * rho g (Pi.single x 1) i := by
      rw [map_sum]
      simp only [Finset.sum_apply,map_smul,Pi.smul_apply,smul_eq_mul]
    _ = v a * rho g (Pi.single a 1) i := hs
    _ = coefficient rho g i * v (g⁻¹ • i) := mul_comm _ _

omit [Fintype I] in
theorem coefficient_one (i : I) : coefficient rho 1 i = 1 := by
  change rho 1 (Pi.single ((1 : G)⁻¹ • i) 1) i = 1
  rw [map_one,Module.End.one_apply,inv_one,one_smul,Pi.single_eq_same]

include hdelta in
/-- The cocycle is inherited from the same actual representation hom. -/
theorem coefficient_mul (g h : G) (i : I) :
    coefficient rho (g*h) i = coefficient rho g i * coefficient rho h (g⁻¹ • i) := by
  calc
    coefficient rho (g*h) i = rho (g*h) (Pi.single ((g*h)⁻¹ • i) 1) i := rfl
    _ = coefficient rho g i * (coefficient rho h (g⁻¹ • i) *
        (Pi.single ((g*h)⁻¹ • i) 1 : I → k) (h⁻¹ • (g⁻¹ • i))) := by
      rw [map_mul,Module.End.mul_apply,action_apply rho hdelta,action_apply rho hdelta]
    _ = coefficient rho g i * coefficient rho h (g⁻¹ • i) := by
      have hidx : (g*h)⁻¹ • i = h⁻¹ • (g⁻¹ • i) := by
        rw [mul_inv_rev,mul_smul]
      have hs : (Pi.single ((g*h)⁻¹ • i) 1 : I → k)
          (h⁻¹ • (g⁻¹ • i)) = 1 := by
        rw [hidx,Pi.single_eq_same]
      exact (congrArg (fun z : k => coefficient rho g i *
        (coefficient rho h (g⁻¹ • i) * z)) hs).trans
          (congrArg (fun z : k => coefficient rho g i * z)
            (mul_one (coefficient rho h (g⁻¹ • i))))

end SymmetricSubgroupAsymptotics.MonomialActualCoefficients
