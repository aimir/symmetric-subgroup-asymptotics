import SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneRootLine
import SymmetricSubgroupAsymptotics.CFSGLinearConjugateDisplacement

/-! The displacement range of each nontrivial actual relative root is
its SAME fixed-field two-plane. This proves the converse to natural
plane determination, without extending scalars or losing Q at p=2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRootPlaneImage
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDHighestPairOperator CFSGTwistedDSingularPlaneOrbit
open CFSGTwistedDPlaneRootLine CFSGTwistedDProjectiveRootFamily CFSGTwistedA2FixedField
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPrefixPerpendicular
open CFSGAlternatingPairOperator CFSGLinearConjugateDisplacement

def negativeBasis (n : ℕ) (q : CFSG.PrimePower) (i : Fin (n + 2)) (hi : i ≠ last n) :
    fixedSpace n q :=
  ⟨Pi.single (Sum.inr i) 1,
    CFSGTwistedDNormalizeFirstPair.fixed_basis (q.Extension 2) n
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) (Sum.inr i)
      (by rw [CFSGTwistedDNaturalFork.flip_neg, if_neg hi])⟩

theorem fixed_pairing_basis (n : ℕ) (q : CFSG.PrimePower)
    (i j : Fin (n + 2)) (hi : i ≠ last n) (hj : j ≠ last n) :
    (fixedQuadraticForm n q).polarBilin (positiveBasis n q i hi) (negativeBasis n q j hj) =
      if i = j then 1 else 0 := by
  apply Subtype.ext
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar]
  change CFSGOrthogonalDIndexPolarForm.polar (q.Extension 2)
    (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1) = _
  rw [polar_positive_basis]
  by_cases h : i = j <;> simp [Pi.single_apply, h]

theorem highestRoot_injective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (highestRoot s q) := by
  intro a b h
  exact CFSGTwistedDRelativeUnipotentCenter.highest_injective s q (Subtype.ext h)

theorem highestRoot_zero (s : ℕ) (q : CFSG.PrimePower) : highestRoot s q 0 = 1 :=
  congrArg Subtype.val (CFSGTwistedDRelativeUnipotentCenter.highest_zero s q)

theorem highest_displacement_range (s : ℕ) (q : CFSG.PrimePower)
    (a : fixedField q) (ha : a ≠ 0) :
    LinearMap.range (displacement (fixedLinearHom (s + 2) q) (highestRoot s q a)) =
      standardRootPlane s q := by
  let e0 := CFSGTwistedDHighestPairOperator.firstVector s q
  let e1 := CFSGTwistedDHighestPairOperator.secondVector s q
  have h0 : (0 : Fin (s + 4)) ≠ last (s + 2) := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = s + 3 at hv
    omega
  have h1 : secondIndex s ≠ last (s + 2) := by
    intro h
    have hv := congrArg Fin.val h
    change 1 = s + 3 at hv
    omega
  let f0 := negativeBasis (s + 2) q 0 h0
  let f1 := negativeBasis (s + 2) q (secondIndex s) h1
  let B := (fixedQuadraticForm (s + 2) q).polarBilin
  have h00 : B e0 f0 = 1 := by
    change (fixedQuadraticForm (s + 2) q).polarBilin
      (positiveBasis (s + 2) q 0 h0) (negativeBasis (s + 2) q 0 h0) = 1
    rw [fixed_pairing_basis, if_pos rfl]
  have h01 : B e0 f1 = 0 := by
    change (fixedQuadraticForm (s + 2) q).polarBilin
      (positiveBasis (s + 2) q 0 h0) (negativeBasis (s + 2) q (secondIndex s) h1) = 0
    rw [fixed_pairing_basis, if_neg (zero_ne_second s)]
  have h10 : B e1 f0 = 0 := by
    change (fixedQuadraticForm (s + 2) q).polarBilin
      (positiveBasis (s + 2) q (secondIndex s) h1) (negativeBasis (s + 2) q 0 h0) = 0
    rw [fixed_pairing_basis, if_neg (Ne.symm (zero_ne_second s))]
  have h11 : B e1 f1 = 1 := by
    change (fixedQuadraticForm (s + 2) q).polarBilin
      (positiveBasis (s + 2) q (secondIndex s) h1)
      (negativeBasis (s + 2) q (secondIndex s) h1) = 1
    rw [fixed_pairing_basis, if_pos rfl]
  have he0 : e0 ∈ standardRootPlane s q := Submodule.subset_span (Or.inl rfl)
  have he1 : e1 ∈ standardRootPlane s q := Submodule.subset_span (Or.inr rfl)
  have hd (v : fixedSpace (s + 2) q) :
      displacement (fixedLinearHom (s + 2) q) (highestRoot s q a) v =
        a • (B e1 v • e0 - B e0 v • e1) :=
    highest_displacement s q a v
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    rw [hd]
    exact (standardRootPlane s q).smul_mem a
      ((standardRootPlane s q).sub_mem
        ((standardRootPlane s q).smul_mem _ he0) ((standardRootPlane s q).smul_mem _ he1))
  · apply Submodule.span_le.mpr
    rintro y (hy | hy)
    · subst y
      refine ⟨a⁻¹ • f1, ?_⟩
      rw [hd]
      simp only [map_smul, h11, h01, smul_eq_mul, mul_one, mul_zero,
        zero_smul, sub_zero, smul_smul, mul_inv_cancel₀ ha, one_smul]
      rfl
    · rcases hy with rfl
      refine ⟨(-a⁻¹) • f0, ?_⟩
      rw [hd]
      simp only [map_smul, h10, h00, smul_eq_mul, mul_zero, mul_one,
        zero_smul, zero_sub]
      change a • -((-(a⁻¹) : fixedField q) • e1) = e1
      have hs : (-(a⁻¹) : fixedField q) • e1 = -(a⁻¹ • e1) := by
        apply Subtype.ext
        funext i
        change (-((a⁻¹ : fixedField q) : q.Extension 2)) * e1.val i =
          -(((a⁻¹ : fixedField q) : q.Extension 2) * e1.val i)
        exact neg_mul _ _
      rw [hs, neg_neg, smul_smul, mul_inv_cancel₀ ha, one_smul]

theorem conjugate_displacement_range (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) (a : fixedField q) (ha : a ≠ 0) :
    LinearMap.range (displacement (fixedLinearHom (s + 2) q)
      (g * highestRoot s q a * g⁻¹)) = conjugateRootPlane s q g := by
  rw [conjugate_range, highest_displacement_range s q a ha]
  rfl

theorem mem_conjugateRootLine_iff (s : ℕ) (q : CFSG.PrimePower)
    (g x : relativeRootGroup (s + 2) q) :
    x ∈ conjugateRootLine s q g ↔
      ∃ a : fixedField q, x = g * highestRoot s q a * g⁻¹ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_highestRootLine_iff s q u).mp hu
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨highestRoot s q a, (mem_highestRootLine_iff s q _).mpr ⟨a, rfl⟩, rfl⟩

theorem conjugateRootPlane_eq_of_rootLine_eq (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q)
    (hL : conjugateRootLine s q g = conjugateRootLine s q h) :
    conjugateRootPlane s q g = conjugateRootPlane s q h := by
  have hx : g * highestRoot s q 1 * g⁻¹ ∈ conjugateRootLine s q g :=
    (mem_conjugateRootLine_iff s q g _).mpr ⟨1, rfl⟩
  rw [hL] at hx
  obtain ⟨b, hb⟩ := (mem_conjugateRootLine_iff s q h _).mp hx
  have hroot : highestRoot s q 1 ≠ 1 := by
    intro hz
    exact one_ne_zero (highestRoot_injective s q (hz.trans (highestRoot_zero s q).symm))
  have hb0 : b ≠ 0 := by
    intro hz
    have hn : g * highestRoot s q 1 * g⁻¹ ≠ 1 := by
      intro he
      exact hroot ((MulAut.conj g).injective (he.trans (MulAut.conj g).map_one.symm))
    apply hn
    rw [hb, hz, highestRoot_zero, mul_one, mul_inv_cancel]
  calc
    conjugateRootPlane s q g = LinearMap.range (displacement (fixedLinearHom (s + 2) q)
        (g * highestRoot s q 1 * g⁻¹)) := (conjugate_displacement_range s q g 1 one_ne_zero).symm
    _ = LinearMap.range (displacement (fixedLinearHom (s + 2) q)
        (h * highestRoot s q b * h⁻¹)) := congrArg
      (fun u => LinearMap.range (displacement (fixedLinearHom (s + 2) q) u)) hb
    _ = conjugateRootPlane s q h := conjugate_displacement_range s q h b hb0

theorem conjugateRootLine_eq_iff_plane_eq (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q) :
    conjugateRootLine s q g = conjugateRootLine s q h ↔
      conjugateRootPlane s q g = conjugateRootPlane s q h :=
  ⟨conjugateRootPlane_eq_of_rootLine_eq s q g h, conjugateRootLine_eq_of_plane_eq s q g h⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDRootPlaneImage
