import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckColumns

/-! Degree twice a norm-two root has just ONE possible matrix position
in the actual Geck Cartan/root basis: v_-a maps to v_a. Unlike ordinary
root degree, this statement holds in the whole surrounding matrix space;
it uses positive-definite integer norms, not generated-Lie recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDoubleRootSupport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckColumns CFSGGradedMatrixSupport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem double_root_weight_pair (a : Roots A) (x y : b.support⊕Roots A)
    (he : latticeWeight A hs hp b x=latticeWeight A hs hp b y+(2:ℤ) • a.val) :
    x=Sum.inr a ∧ y=Sum.inr (negativeIndex A hs hp a) := by
  have htwo : integerPairing A ((2:ℤ) • a.val) ((2:ℤ) • a.val)=8 := by
    simp only [(integerPairing A).smul_left,(integerPairing A).smul_right,a.property]
    norm_num
  cases x with
  | inl i=>
    cases y with
    | inl j=>
      change (0 : n→ℤ)=0+(2:ℤ) • a.val at he
      have hz : (2:ℤ) • a.val=0 := by simpa only [zero_add] using he.symm
      have hh := congrArg (fun v : n→ℤ=>integerPairing A v v) hz
      dsimp only at hh
      rw [htwo] at hh
      norm_num at hh
    | inr k=>
      change (0 : n→ℤ)=k.val+(2:ℤ) • a.val at he
      have hk : k.val= -((2:ℤ) • a.val) := eq_neg_iff_add_eq_zero.mpr he.symm
      have hn := k.property
      rw [hk] at hn
      simp only [map_neg,LinearMap.neg_apply,neg_neg] at hn
      rw [htwo] at hn
      norm_num at hn
  | inr k=>
    cases y with
    | inl j=>
      change k.val=0+(2:ℤ) • a.val at he
      have hk : k.val=(2:ℤ) • a.val := by simpa only [zero_add] using he
      have hn := k.property
      rw [hk,htwo] at hn
      norm_num at hn
    | inr l=>
      change k.val=l.val+(2:ℤ) • a.val at he
      have hn := k.property
      rw [he,norm_add A hs,l.property,htwo] at hn
      have hbil : integerPairing A l.val ((2:ℤ) • a.val)=2*integerPairing A l.val a.val := by
        rw [(integerPairing A).smul_right]
      rw [hbil] at hn
      have hpair : integerPairing A l.val a.val= -2 := by omega
      have hl := (root_pairing_eq_neg_two_iff A hs hp l a).mp hpair
      constructor
      · apply congrArg Sum.inr
        apply Subtype.ext
        rw [he,hl,two_smul]
        abel
      · apply congrArg Sum.inr
        apply Subtype.ext
        exact hl.trans (negative_val A hs hp a).symm

theorem double_root_supported_single {R : Type*} [Semiring R] (a : Roots A)
    (M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) R)
    (hM : Supported (latticeWeight A hs hp b) (fun v=>v+(2:ℤ) • a.val) M) :
    M=Matrix.single (Sum.inr a) (Sum.inr (negativeIndex A hs hp a))
      (M (Sum.inr a) (Sum.inr (negativeIndex A hs hp a))) := by
  ext x y
  by_cases hx : x=Sum.inr a
  · by_cases hy : y=Sum.inr (negativeIndex A hs hp a)
    · subst x
      subst y
      simp [Matrix.single_apply]
    · have he : latticeWeight A hs hp b x≠latticeWeight A hs hp b y+(2:ℤ) • a.val := by
        intro he
        exact hy (double_root_weight_pair A hs hp b a x y he).2
      have hno : ¬(Sum.inr a=x ∧ Sum.inr (negativeIndex A hs hp a)=y) :=
        fun h=>hy h.2.symm
      rw [Matrix.single_apply,if_neg hno]
      exact hM x y he
  · have he : latticeWeight A hs hp b x≠latticeWeight A hs hp b y+(2:ℤ) • a.val := by
      intro he
      exact hx (double_root_weight_pair A hs hp b a x y he).1
    have hno : ¬(Sum.inr a=x ∧ Sum.inr (negativeIndex A hs hp a)=y) :=
      fun h=>hx h.1.symm
    rw [Matrix.single_apply,if_neg hno]
    exact hM x y he

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDoubleRootSupport
