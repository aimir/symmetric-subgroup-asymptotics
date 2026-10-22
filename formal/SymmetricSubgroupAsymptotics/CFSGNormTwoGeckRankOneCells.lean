import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleRootCells
import SymmetricSubgroupAsymptotics.CFSGRankOneBruhatClosure

/-! Actual rank-one cell multiplication for the WHOLE positive group.
The proof retains the original Weyl square in the actual torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneCells
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveComplement
open CFSGNormTwoGeckComplementNormalizer CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckParameterizedWeyl CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckWeylSquareTorus CFSGNormTwoGeckTorusConjugation
open CFSGNormTwoGeckSimpleRootCells CFSGRankOneBruhat
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem weyl_square_mem_torus (K : Type) [Field K] (i : Fin r) :
    (canonicalWeyl (realizationData A hs hp b s) K i)^2∈torusGroup A hs hp b s K := by
  rw [←torus_neg_one_eq_square A hs hp b s K i]
  exact Subgroup.subset_closure ⟨(i,-1),rfl⟩

theorem square_conjugate_self (K : Type) [Field K] (i : Fin r) (a : K) :
    (canonicalWeyl (realizationData A hs hp b s) K i)^2*
      canonicalRoot (realizationData A hs hp b s) K false i a*
      ((canonicalWeyl (realizationData A hs hp b s) K i)^2)⁻¹=
      canonicalRoot (realizationData A hs hp b s) K false i a := by
  have hh := torus_conjugate_positive A hs hp b s K i i (-1) a
  rw [torus_neg_one_eq_square,(s i:Roots A).property] at hh
  simpa only [Units.val_neg,Units.val_one,zpow_ofNat,neg_one_sq,mul_one] using hh

theorem weyl_simple_cell (K : Type) [Field K] (i : Fin r) (a : K) :
    Cell (borelEnvelope A hs hp b s K) (rootGroup A hs hp b s K false)
      (canonicalWeyl (realizationData A hs hp b s) K i)
      (canonicalWeyl (realizationData A hs hp b s) K i*
        canonicalRoot (realizationData A hs hp b s) K false i a*
        canonicalWeyl (realizationData A hs hp b s) K i) := by
  let D := realizationData A hs hp b s
  let w := canonicalWeyl D K i
  have hwT : w^2∈torusGroup A hs hp b s K := weyl_square_mem_torus A hs hp b s K i
  have hwB : w^2∈borelEnvelope A hs hp b s K :=
    (show torusGroup A hs hp b s K≤borelEnvelope A hs hp b s K from le_sup_right) hwT
  by_cases ha : a=0
  · subst a
    left
    simpa only [canonicalRoot_zero,mul_one,←pow_two] using hwB
  let t : Kˣ := Units.mk0 a⁻¹ (inv_ne_zero ha)
  let u := canonicalRoot D K false i (t:K)
  let l := u⁻¹*parameterTorus A hs hp b s K i t
  have hu : u∈rootGroup A hs hp b s K false := Subgroup.subset_closure ⟨(i,(t:K)),rfl⟩
  have huB : u∈borelEnvelope A hs hp b s K :=
    (show rootGroup A hs hp b s K false≤borelEnvelope A hs hp b s K from le_sup_left) hu
  have htB : parameterTorus A hs hp b s K i t∈borelEnvelope A hs hp b s K :=
    (show torusGroup A hs hp b s K≤borelEnvelope A hs hp b s K from le_sup_right)
      (Subgroup.subset_closure ⟨(i,t),rfl⟩)
  have hl : l∈borelEnvelope A hs hp b s K :=
    (borelEnvelope A hs hp b s K).mul_mem ((borelEnvelope A hs hp b s K).inv_mem huB) htB
  have hn : canonicalRoot D K true i (-a)=l*w*u⁻¹ := by
    have hta : -(t:K)⁻¹= -a := by change -(a⁻¹)⁻¹= -a; simp
    change canonicalRoot D K true i (-a)=
      (u⁻¹*(parameterWeyl A hs hp b s K i t*(parameterWeyl A hs hp b s K i 1)⁻¹))*w*u⁻¹
    rw [parameterWeyl_one,←hta]
    dsimp only [parameterWeyl,u,w,D]
    group
  have hc : w^2*u⁻¹*(w^2)⁻¹=u⁻¹ := by
    simpa only [u,w,D,canonicalRoot_inverse] using square_conjugate_self A hs hp b s K i (-(t:K))
  have hr : u⁻¹*w^2=w^2*u⁻¹ := by
    have hh := congrArg (fun z=>z*w^2) hc
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm
  have he : w*canonicalRoot D K false i a*w=(l*w^2)*w*u⁻¹ := by
    calc
      _=(w*canonicalRoot D K false i a*w⁻¹)*w^2 := by simp only [pow_two]; group
      _=canonicalRoot D K true i (-a)*w^2 := by
        rw [CFSGNormTwoGeckSelfRootConjugation.self_root_word A hs hp b s K i a]
      _=(l*w*u⁻¹)*w^2 := by rw [hn]
      _=(l*w^2)*w*u⁻¹ := by rw [mul_assoc,mul_assoc,hr]; simp only [pow_two]; group
  exact Or.inr ⟨l*w^2,(borelEnvelope A hs hp b s K).mul_mem hl hwB,
    u⁻¹,(rootGroup A hs hp b s K false).inv_mem hu,he⟩

theorem weyl_positive_cell (K : Type) [Field K] (i : Fin r)
    (u : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hu : u∈rootGroup A hs hp b s K false) :
    Cell (borelEnvelope A hs hp b s K) (rootGroup A hs hp b s K false)
      (canonicalWeyl (realizationData A hs hp b s) K i)
      (canonicalWeyl (realizationData A hs hp b s) K i*u*
        canonicalWeyl (realizationData A hs hp b s) K i) := by
  obtain ⟨v,hv,a,rfl⟩ := positive_factor A hs hp b s K i u hu
  have hvc := weyl_conjugate_mem A hs hp b s K i v hv
  have hvU := complement_le_positive A hs hp b s K i hvc
  have hvB := (show rootGroup A hs hp b s K false≤borelEnvelope A hs hp b s K from le_sup_left) hvU
  have hh := cell_left_mul (borelEnvelope A hs hp b s K) (rootGroup A hs hp b s K false)
    (canonicalWeyl (realizationData A hs hp b s) K i) _ _ hvB
    (weyl_simple_cell A hs hp b s K i a)
  have he :
      (canonicalWeyl (realizationData A hs hp b s) K i*v*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹)*
      (canonicalWeyl (realizationData A hs hp b s) K i*
        canonicalRoot (realizationData A hs hp b s) K false i a*
        canonicalWeyl (realizationData A hs hp b s) K i)=
      canonicalWeyl (realizationData A hs hp b s) K i*
        (v*canonicalRoot (realizationData A hs hp b s) K false i a)*
        canonicalWeyl (realizationData A hs hp b s) K i := by group
  rw [he] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneCells
