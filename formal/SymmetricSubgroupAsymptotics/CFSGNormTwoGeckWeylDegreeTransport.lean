import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSignedRootColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylCartan

/-! Actual Weyl conjugation transports every homogeneous lattice degree
by the original integral reflection. This supplies degree control for
longer Weyl words without a root-space recognition assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylDegreeTransport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckSignedRootColumns CFSGNormTwoGeckFieldWeylCartan
open CFSGNormTwoGeckWeylUnits CFSGSerreQuadraticMatrix CFSGGradedMatrixSupport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem weyl_lattice_support (K : Type*) [CommRing K] (i : Fin r) :
    Supported (latticeWeight A hs hp b) (reflectionEquiv A (s i))
      (canonicalWeyl (realizationData A hs hp b s) K i :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := by
  intro j k hjk
  cases k with
  | inl k=>
    have hc := weyl_cartan_general A hs hp b s K i k
    rw [Matrix.mulVec_single_one] at hc
    have he := congrFun hc j
    cases j with
    | inl j=>exact False.elim (hjk (map_zero _).symm)
    | inr j=>simpa [Pi.single_apply] using he
  | inr k=>
    obtain ⟨c,_,hc⟩ := signed_root_column A hs hp b s K i k
    rw [Matrix.mulVec_single_one] at hc
    have he := congrFun hc j
    have hwt : latticeWeight A hs hp b
        (.inr ((rootPairing A hs hp).reflectionPerm (s i) k))=
        reflectionEquiv A (s i) (latticeWeight A hs hp b (.inr k)) := rfl
    have hne : j≠.inr ((rootPairing A hs hp).reflectionPerm (s i) k) := by
      intro h
      subst j
      exact hjk hwt
    simpa [Pi.single_apply,hne,Ne.symm hne] using he

theorem weyl_inverse_lattice_support (K : Type*) [CommRing K] (i : Fin r) :
    Supported (latticeWeight A hs hp b) (reflectionEquiv A (s i)).symm
      (↑((canonicalWeyl (realizationData A hs hp b s) K i)⁻¹) :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := by
  let w := canonicalWeyl (realizationData A hs hp b s) K i
  have hw : Supported (latticeWeight A hs hp b) (reflectionEquiv A (s i))
      (w : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) :=
    weyl_lattice_support A hs hp b s K i
  have h2 : Supported (latticeWeight A hs hp b) id
      ((w : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
        (w : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)) := by
    apply supported_congr (supported_mul hw hw)
    intro v
    exact (reflectionEquiv A (s i)).left_inv v
  have h3 : Supported (latticeWeight A hs hp b) (reflectionEquiv A (s i))
      ((w : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
        (w : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
        (w : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)) :=
    supported_congr (supported_mul h2 hw) (fun _=>rfl)
  have hinv : w⁻¹=w*w*w := by
    apply inv_eq_of_mul_eq_one_right
    calc
      w*(w*w*w)=w^4 := by simp only [pow_succ,pow_zero,one_mul,mul_assoc]
      _=1 := weyl_four A hs hp b s K i
  change Supported (latticeWeight A hs hp b) (reflectionEquiv A (s i)).symm
    (↑(w⁻¹) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
  rw [hinv,Units.val_mul,Units.val_mul]
  exact h3

theorem conjugate_homogeneous (K : Type*) [CommRing K] (i : Fin r)
    (d : n→ℤ) (M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
    (hM : Supported (latticeWeight A hs hp b) (fun w=>w+d) M) :
    Supported (latticeWeight A hs hp b)
      (fun w=>w+reflectionEquiv A (s i) d)
      ((canonicalWeyl (realizationData A hs hp b s) K i :
          Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*M*
        (↑((canonicalWeyl (realizationData A hs hp b s) K i)⁻¹) :
          Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)) :=
  supported_conjugation _ (reflectionEquiv A (s i)) d _ _ _
    (weyl_lattice_support A hs hp b s K i) hM
    (weyl_inverse_lattice_support A hs hp b s K i)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylDegreeTransport
