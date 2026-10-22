import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerCartan
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerOutside

/-! Whole-space Singer power seven, proved on the original norm-two Geck
basis using the six A2 roots, seven outside weights, and Cartan complement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerSeven
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylCharTwoRoots CFSGNormTwoRootStepCoordinates
open CFSGNormTwoGeckSingerFirstBlock CFSGNormTwoGeckSingerSecondBlock
open CFSGNormTwoGeckSingerAdjoint CFSGNormTwoGeckSingerCartan
open CFSGNormTwoGeckSingerOutside CFSGNormTwoGeckPairingUnitColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

private theorem power_fixed {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (x : M) (hx : f x=x) : ∀ k : ℕ, (f^k) x=x := by
  intro k
  induction k with
  | zero => rfl
  | succ k hk => rw [pow_succ,Module.End.mul_apply,hx,hk]

private theorem singer_zero_weight (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (k : Roots A) (hik : integerPairing A (s i:Roots A).val k.val=0)
    (hjk : integerPairing A (s j:Roots A).val k.val=0) :
    ((singerOperator A hs hp b s K i j)^7) (Pi.single (.inr k) 1)=Pi.single (.inr k) 1 := by
  apply power_fixed
  change ((canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*
    (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
    (canonicalWeyl (realizationData A hs hp b s) K j : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K))*ᵥ
      Pi.single (.inr k) 1=_
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,weyl_root_column,
    reflection_fixed A hs hp (s j) k hjk,weyl_root_column,reflection_fixed A hs hp (s i) k hik]
  exact unit_fixed_of_pairing A hs hp b s K i k (by omega) (by omega)

theorem singer_root_seven (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1)
    (gamma : Roots A)
    (hg : (rootPairing A hs hp).root gamma=
      (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root (s j))
    (k : Roots A) :
    ((singerOperator A hs hp b s K i j)^7) (Pi.single (.inr k) 1)=Pi.single (.inr k) 1 := by
  by_cases hi : k=(s i:Roots A)
  · subst k;exact singer_adjoint_seven A hs hp b s K i j hij gamma hg 2
  by_cases hj : k=(s j:Roots A)
  · subst k;exact singer_adjoint_seven A hs hp b s K i j hij gamma hg 3
  by_cases hgamma : k=gamma
  · subst k;exact singer_adjoint_seven A hs hp b s K i j hij gamma hg 4
  by_cases hni : k=negativeIndex A hs hp (s i)
  · subst k;exact singer_adjoint_seven A hs hp b s K i j hij gamma hg 5
  by_cases hnj : k=negativeIndex A hs hp (s j)
  · subst k;exact singer_adjoint_seven A hs hp b s K i j hij gamma hg 6
  by_cases hng : k=negativeIndex A hs hp gamma
  · subst k;exact singer_adjoint_seven A hs hp b s K i j hij gamma hg 7
  have hniv : k.val≠ -(s i:Roots A).val := by
    intro he;apply hni;apply Subtype.ext;rw [negative_val];exact he
  have hnjv : k.val≠ -(s j:Roots A).val := by
    intro he;apply hnj;apply Subtype.ext;rw [negative_val];exact he
  have hngv : k.val≠ -gamma.val := by
    intro he;apply hng;apply Subtype.ext;rw [negative_val];exact he
  rcases CFSGNormTwoA2WeightCases.outside_weights A hs hp (s i) (s j) gamma k
    hg hi hj hgamma hniv hnjv hngv with h|h|h|h|h|h|h
  · exact singer_zero_weight A hs hp b s K i j k h.1 h.2
  · exact singer_first_block A hs hp b s K i j hij k h.1 h.2
  · exact singer_weight_one_neg_one A hs hp b s K i j hij k h.1 h.2
  · exact singer_weight_zero_one A hs hp b s K i j hij k h.1 h.2
  · exact singer_second_block A hs hp b s K i j hij k h.1 h.2
  · exact singer_weight_zero_neg_one A hs hp b s K i j hij k h.1 h.2
  · exact singer_weight_one_zero A hs hp b s K i j hij k h.1 h.2

theorem canonical_singer_seven (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1) :
    (canonicalRoot (realizationData A hs hp b s) K false i 1*
      canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalWeyl (realizationData A hs hp b s) K j)^7=1 := by
  obtain ⟨gamma,hg⟩ := (CFSGNormTwoRootNeighbors.root_add_mem_iff A hs hp (s i) (s j)).mpr hij
  let w := canonicalRoot (realizationData A hs hp b s) K false i 1*
    canonicalWeyl (realizationData A hs hp b s) K i*
    canonicalWeyl (realizationData A hs hp b s) K j
  have he : Matrix.toLinAlgEquiv' ((w^7 : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ) :
      Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)=(singerOperator A hs hp b s K i j)^7 := by
    change Matrix.toLinAlgEquiv' ((w : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)^7)=_
    rw [map_pow]
    rfl
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro z
  rw [Units.val_one,Matrix.one_mulVec]
  have hx := congrArg (fun f : Module.End K (b.support⊕Roots A→K)=>f (Pi.single z 1)) he
  change ((w^7 : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ) :
    Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single z 1=
    ((singerOperator A hs hp b s K i j)^7) (Pi.single z 1) at hx
  rw [hx]
  rcases z with k|k
  · exact singer_cartan_seven A hs hp b s K i j hij gamma hg k
  · exact singer_root_seven A hs hp b s K i j hij gamma hg k

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerSeven
