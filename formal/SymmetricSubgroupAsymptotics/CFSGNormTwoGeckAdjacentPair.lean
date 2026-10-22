import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointWeylPair
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalWeylCollecting
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticOrthogonalCollecting

/-! Two adjacent actual simple Weyl words carry the first simple root
line to the second, with its parameter unchanged. The proof uses both
columns of the rational A2 adjoint string, then integer polynomial
transport; no scalar uniqueness of homogeneous operators is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentPair
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoGeckRationalWeylCollecting
open CFSGSerreQuadraticAdjointWeylPair
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s

theorem rational_pair_coefficient (i j : Fin r)
    (hij : cartan b s i j= -1) (hji : cartan b s j i= -1) :
    ((canonicalWeyl D ℚ i*canonicalWeyl D ℚ j : (Target b)ˣ) : Target b)*
      fieldRoot D ℚ false i*
        (((canonicalWeyl D ℚ i*canonicalWeyl D ℚ j)⁻¹ : (Target b)ˣ) : Target b)=
      fieldRoot D ℚ false j := by
  let e := CFSGAlgebraConjugationAction.action ℚ (Target b)
  have hj : e (canonicalWeyl D ℚ j) (fieldRoot D ℚ false i)=
      -⁅fieldRoot D ℚ false i,fieldRoot D ℚ false j⁆ := by
    have hh := weyl_conjugate_adjacent A hs hp b s j i hji
    have hh' : e (canonicalWeyl D ℚ j) (fieldRoot D ℚ false i)=
        ⁅fieldRoot D ℚ false j,fieldRoot D ℚ false i⁆ := by
      simpa only [CFSGNormTwoGeckParameterizedWeyl.parameterWeyl,canonicalWeyl,
        Units.val_one,inv_one] using hh
    exact hh'.trans (lie_skew _ _).symm
  have hi : e (canonicalWeyl D ℚ i)
      ⁅fieldRoot D ℚ false i,fieldRoot D ℚ false j⁆= -fieldRoot D ℚ false j :=
    weyl_on_second D i (fieldRoot D ℚ false j)
      ⁅fieldRoot D ℚ false i,fieldRoot D ℚ false j⁆ rfl
      (double_lie_of_cartan_neg_one A hs hp b s i j hij)
      (F_E_ne A hs hp b s i j (indices_ne_of_cartan_neg_one A hs hp b s i j hij))
      (F_EE_adjacent A hs hp b s i j hij)
  change e (canonicalWeyl D ℚ i*canonicalWeyl D ℚ j) (fieldRoot D ℚ false i)=_
  rw [map_mul]
  change e (canonicalWeyl D ℚ i) (e (canonicalWeyl D ℚ j) (fieldRoot D ℚ false i))=_
  rw [hj,map_neg,hi,neg_neg]

def pairWord (K : Type*) [CommRing K] (i j : Fin r) (a : K) :
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  (canonicalWeyl D K i*canonicalWeyl D K j)*canonicalRoot D K false i a*
    (canonicalWeyl D K i*canonicalWeyl D K j)⁻¹

theorem rational_pair_word (i j : Fin r)
    (hij : cartan b s i j= -1) (hji : cartan b s j i= -1) (a : ℚ) :
    pairWord A hs hp b s ℚ i j a=canonicalRoot D ℚ false j a := by
  apply Units.ext
  change ((canonicalWeyl D ℚ i*canonicalWeyl D ℚ j : (Target b)ˣ) : Target b)*
    (canonicalRoot D ℚ false i a : Target b)*
      (((canonicalWeyl D ℚ i*canonicalWeyl D ℚ j)⁻¹ : (Target b)ˣ) : Target b)=_
  simp only [canonicalRoot_val_rational]
  exact CFSGUnitConjugationPolynomial.conjugate_quadratic
    (canonicalWeyl D ℚ i*canonicalWeyl D ℚ j)
    (fieldRoot D ℚ false i) (fieldRoot D ℚ false j)
    (rational_pair_coefficient A hs hp b s i j hij hji) a

theorem map_pairWord_val {K L : Type*} [CommRing K] [CommRing L]
    (f : K→+*L) (i j : Fin r) (a : K) :
    f.mapMatrix (pairWord A hs hp b s K i j a : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)=
      (pairWord A hs hp b s L i j (f a) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) L) := by
  simp only [pairWord,mul_inv_rev,Units.val_mul,map_mul,map_canonicalWeyl_val,
    map_canonicalWeyl_inv_val,map_canonicalRoot_val]

theorem adjacent_pair_word (K : Type*) [CommRing K] (i j : Fin r)
    (hij : cartan b s i j= -1) (hji : cartan b s j i= -1) (a : K) :
    (canonicalWeyl D K i*canonicalWeyl D K j)*canonicalRoot D K false i a*
      (canonicalWeyl D K i*canonicalWeyl D K j)⁻¹=canonicalRoot D K false j a := by
  let M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) (Polynomial ℤ) :=
    pairWord A hs hp b s (Polynomial ℤ) i j Polynomial.X
  let N : Matrix (b.support⊕Roots A) (b.support⊕Roots A) (Polynomial ℤ) :=
    canonicalRoot D (Polynomial ℤ) false j Polynomial.X
  have hh : ∀c : ℚ,(Polynomial.eval₂RingHom (Int.castRingHom ℚ) c).mapMatrix M=
      (Polynomial.eval₂RingHom (Int.castRingHom ℚ) c).mapMatrix N := by
    intro c
    dsimp only [M,N]
    simpa only [map_pairWord_val,map_canonicalRoot_val,
      Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using
      congrArg (fun u : (Target b)ˣ=>(u : Target b))
        (rational_pair_word A hs hp b s i j hij hji c)
  have hk := CFSGIntegerMatrixPolynomialTransport.evaluations_eq_of_rational_evaluations K M N hh a
  apply Units.ext
  dsimp only [M,N] at hk
  simpa only [map_pairWord_val,map_canonicalRoot_val,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using hk

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentPair
