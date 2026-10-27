import SymmetricSubgroupAsymptotics.FiniteIntegralFamilySaturatedSpan
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice
import Mathlib.Algebra.Module.Torsion.Free

/-! For the SAME original integral Serre lattice, a primitive realized
finite family needs only FIRST simple-root action stability. Saturation
then cancels every factorial and supplies all divided-power stability.
No cubic table or inverse of 2 in the coefficient field is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreSaturatedFirstActionSpan
open CFSG.Models.Chevalley CFSGSerreDiagram
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)

private theorem first_val (neg : Bool) (i : Fin r) (x : integralLattice A) :
    (integralOperator A neg i 1 x).val=⁅rootVector A neg i,x.val⁆ := by
  change ((Nat.factorial 1:ℚ)⁻¹) •
    (LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i)^1) x.val = _
  simp only [Nat.factorial_one,Nat.cast_one,inv_one,pow_one,one_smul,
    LieAlgebra.ad_apply]

private theorem first_power_val (neg : Bool) (i : Fin r) (k : ℕ)
    (x : integralLattice A) :
    (((integralOperator A neg i 1)^k) x).val=
      (LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i)^k) x.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ',Module.End.mul_apply,first_val,LieAlgebra.ad_apply,ih]

theorem factorial_nsmul_operator (neg : Bool) (i : Fin r) (k : ℕ)
    (x : integralLattice A) :
    k.factorial • integralOperator A neg i k x=((integralOperator A neg i 1)^k) x := by
  apply Subtype.ext
  change k.factorial • (integralOperator A neg i k x).val = _
  rw [←Nat.cast_smul_eq_nsmul ℚ,first_power_val]
  change (k.factorial:ℚ) • (((k.factorial:ℚ)⁻¹) •
    (LieAlgebra.ad ℚ (RationalLie A) (rootVector A neg i)^k) x.val) = _
  rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k),one_smul]

theorem nsmul_injective (n : ℕ) (hn : n≠0) :
    Function.Injective (fun x : integralLattice A=>n • x) := by
  intro x y h
  apply Subtype.ext
  have hv:=congrArg Subtype.val h
  change n • x.val=n • y.val at hv
  apply smul_right_injective (RationalLie A) (show (n:ℚ)≠0 by exact_mod_cast hn)
  simpa only [Nat.cast_smul_eq_nsmul] using hv

variable {J N : Type*} [Fintype J] [DecidableEq J]
    [AddCommGroup N] [Module ℤ N]
    (f : integralLattice A→ₗ[ℤ]N) (v : J→integralLattice A)
    (c : N→ₗ[ℤ](J→ℤ))
    (hcoord : ∀ j,c (f (v j))=Pi.single j 1)
    (hfirst : ∀ neg i j,integralOperator A neg i 1 (v j)∈
      Submodule.span ℤ (Set.range v))
include hcoord hfirst

theorem dividedPower_stable (neg : Bool) (i : Fin r) (k : ℕ)
    (x : integralLattice A) (hx : x∈Submodule.span ℤ (Set.range v)) :
    integralOperator A neg i k x∈Submodule.span ℤ (Set.range v) := by
  have hD : ∀ y∈Submodule.span ℤ (Set.range v),
      integralOperator A neg i 1 y∈Submodule.span ℤ (Set.range v) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨j,rfl⟩:=hy; exact hfirst neg i j
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  have hp : ∀ k : ℕ,((integralOperator A neg i 1)^k) x∈Submodule.span ℤ (Set.range v) := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih => rw [pow_succ',Module.End.mul_apply]; exact hD _ ih
  apply FiniteIntegralFamilySaturatedSpan.saturated f v c hcoord
    (nsmul_injective A) k.factorial (Nat.factorial_ne_zero k)
  rw [factorial_nsmul_operator]
  exact hp k

/-- Exact original source spanning, proved from actual first action tables. -/
theorem span_eq_top
    (hgen : ∀ g,latticeGenerator A g∈Submodule.span ℤ (Set.range v)) :
    Submodule.span ℤ (Set.range v)=⊤ := by
  let S:=Submodule.span ℤ (Set.range v)
  let T:=S.map (integralLattice A).subtype
  have hle : integralLattice A≤T := by
    apply integralLattice_le_of_stable A T
    · intro g
      exact ⟨latticeGenerator A g,hgen g,rfl⟩
    · intro neg i k y hy
      obtain ⟨x,hx,rfl⟩:=hy
      exact ⟨integralOperator A neg i k x,
        dividedPower_stable A f v c hcoord hfirst neg i k x hx,rfl⟩
  apply top_unique
  intro x hx
  obtain ⟨y,hy,he⟩:=hle x.property
  have he' : y=x := Subtype.ext he
  exact he' ▸ hy

theorem realization_injective
    (hgen : ∀ g,latticeGenerator A g∈Submodule.span ℤ (Set.range v)) :
    Function.Injective f :=
  FiniteIntegralFamilySplitRealization.injective f v c
    (span_eq_top A f v c hcoord hfirst hgen) hcoord

theorem baseChange_injective
    (hgen : ∀ g,latticeGenerator A g∈Submodule.span ℤ (Set.range v))
    (K : Type*) [CommRing K] : Function.Injective (f.baseChange K) :=
  FiniteIntegralFamilySplitRealization.baseChange_injective f v c
    (span_eq_top A f v c hcoord hfirst hgen) hcoord K

end SymmetricSubgroupAsymptotics.CFSGSerreSaturatedFirstActionSpan
