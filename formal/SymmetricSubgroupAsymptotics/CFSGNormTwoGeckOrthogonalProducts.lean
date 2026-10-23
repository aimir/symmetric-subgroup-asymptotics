import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeightDiameter
import SymmetricSubgroupAsymptotics.CFSGNormTwoOrthogonalOrbitNorms

/-! Products of a second-root degree and an orthogonal first/second
degree vanish on the literal Geck Cartan/root module, over every ring.
The proof uses norms ten and sixteen beyond its squared diameter eight;
there is no division or generated-Lie membership assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalProducts
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base) {K : Type*} [Semiring K]

theorem supported_product_zero (d e : n→ℤ)
    (M N : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
    (hM : Supported (latticeWeight A hs hp b) (fun v=>v+d) M)
    (hN : Supported (latticeWeight A hs hp b) (fun v=>v+e) N)
    (hnorm : 8 < integerPairing A (d+e) (d+e)) : M*N=0 := by
  apply CFSGNormTwoGeckWeightDiameter.supported_eq_zero_of_norm_gt_eight
    A hs hp b (d+e) hnorm (M*N)
  apply supported_congr (supported_mul hM hN)
  intro v
  dsimp only [Function.comp_apply]
  abel

theorem second_mul_orthogonal_first_zero (a c : Roots A)
    (hac : integerPairing A a.val c.val=0)
    (D E : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
    (hD : Supported (latticeWeight A hs hp b) (fun v=>v+(2:ℤ) • a.val) D)
    (hE : Supported (latticeWeight A hs hp b) (fun v=>v+c.val) E) : D*E=0 := by
  apply supported_product_zero A hs hp b ((2:ℤ) • a.val) c.val D E hD hE
  rw [CFSGNormTwoOrthogonalOrbitNorms.double_orthogonal_norm A hs a c hac]
  norm_num

theorem first_mul_orthogonal_second_zero (a c : Roots A)
    (hac : integerPairing A a.val c.val=0)
    (E D : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
    (hE : Supported (latticeWeight A hs hp b) (fun v=>v+c.val) E)
    (hD : Supported (latticeWeight A hs hp b) (fun v=>v+(2:ℤ) • a.val) D) : E*D=0 := by
  apply supported_product_zero A hs hp b c.val ((2:ℤ) • a.val) E D hE hD
  rw [add_comm c.val ((2:ℤ) • a.val),
    CFSGNormTwoOrthogonalOrbitNorms.double_orthogonal_norm A hs a c hac]
  norm_num

theorem second_mul_orthogonal_second_zero (a c : Roots A)
    (hac : integerPairing A a.val c.val=0)
    (D H : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
    (hD : Supported (latticeWeight A hs hp b) (fun v=>v+(2:ℤ) • a.val) D)
    (hH : Supported (latticeWeight A hs hp b) (fun v=>v+(2:ℤ) • c.val) H) : D*H=0 := by
  apply supported_product_zero A hs hp b ((2:ℤ) • a.val) ((2:ℤ) • c.val) D H hD hH
  have hnorm : integerPairing A ((2:ℤ) • a.val+(2:ℤ) • c.val)
      ((2:ℤ) • a.val+(2:ℤ) • c.val)=16 := by
    simp only [map_add,LinearMap.add_apply,(integerPairing A).smul_left,
      (integerPairing A).smul_right,smul_eq_mul]
    rw [a.property,c.property,hac,integer_symmetric A hs c.val a.val,hac]
    norm_num
  rw [hnorm]
  norm_num

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalProducts
