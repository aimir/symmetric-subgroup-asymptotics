import SymmetricSubgroupAsymptotics.CFSGIntegerVectorPolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum

/-! A positive integer linear functional separates any finite set of
integer vectors. Nonzero difference polynomials have finitely many roots;
the chosen integer exceeds the absolute values of their whole finite
union. No vector-coordinate bound or sample evaluation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.CFSGFiniteIntegerPositiveSeparator
open CFSGIntegerVectorPolynomial
variable {r : ℕ}

def badRoots (S : Finset (Fin r→ℤ)) : Finset ℤ :=
  S.biUnion (fun x=>S.biUnion (fun y=>(codePolynomial x-codePolynomial y).roots.toFinset))

def separatorParameter (S : Finset (Fin r→ℤ)) : ℤ :=
  (max 2 ((badRoots S).sup Int.natAbs+1) : ℕ)

theorem separatorParameter_gt_one (S : Finset (Fin r→ℤ)) : 1<separatorParameter S := by
  have hm : 2≤max 2 ((badRoots S).sup Int.natAbs+1) := le_max_left _ _
  change (1:ℤ)<((max 2 ((badRoots S).sup Int.natAbs+1) : ℕ) : ℤ)
  omega

theorem separatorParameter_not_bad (S : Finset (Fin r→ℤ)) :
    separatorParameter S∉badRoots S := by
  intro h
  have hb := Finset.le_sup (s:=badRoots S) (f:=Int.natAbs) h
  have hm : max 2 ((badRoots S).sup Int.natAbs+1)≤(badRoots S).sup Int.natAbs := by
    simpa only [separatorParameter,Int.natAbs_natCast] using hb
  omega

theorem separator_injective (S : Finset (Fin r→ℤ)) :
    Set.InjOn (weightedSum (separatorParameter S) : (Fin r→ℤ)→ℤ) (S : Set (Fin r→ℤ)) := by
  intro x hx y hy he
  by_contra hxy
  have hp : codePolynomial x-codePolynomial y≠0 := by
    apply sub_ne_zero.mpr
    intro h
    exact hxy (codePolynomial_injective h)
  have hz : (codePolynomial x-codePolynomial y).eval (separatorParameter S)=0 := by
    rw [Polynomial.eval_sub,eval_codePolynomial,eval_codePolynomial,he,sub_self]
  have hroot : separatorParameter S∈(codePolynomial x-codePolynomial y).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hz)
  apply separatorParameter_not_bad S
  exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_biUnion.mpr ⟨y,hy,hroot⟩⟩

theorem exists_positive_linear_separator (S : Finset (Fin r→ℤ)) :
    ∃ell : (Fin r→ℤ)→ₗ[ℤ]ℤ,
      (∀i,0<ell (Pi.single i (1:ℤ))) ∧ Set.InjOn ell (S : Set (Fin r→ℤ)) := by
  refine ⟨weightedSum (separatorParameter S),?_,separator_injective S⟩
  intro i
  exact weightedSum_single_pos (separatorParameter S)
    (lt_trans (by decide : (0:ℤ)<1) (separatorParameter_gt_one S)) i

end SymmetricSubgroupAsymptotics.CFSGFiniteIntegerPositiveSeparator
