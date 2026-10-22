import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootFamilyBruhatCover

/-! A finite symbolic bound for the actual dominant-root conjugacy
family. Every factor and cover comes from the original Geck matrices;
only a numerical commuting-root census remains to specialize. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootFamilyCardinality
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateRootFamilyBruhatCover
open CFSGNormTwoCoordinatePositiveRootOrbitCardinality
open CFSGNormTwoCoordinateRootCentralizerCardinality CFSGNormTwoCoordinatePositiveRootGenerators
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

def rootConjugateFamily (K : Type) [Field K] (θ : Roots A) :=
  Set.range (fun g : ElementaryGroup A hd hs hp ho K=>
    (rootSubgroup A hd hs hp ho K θ).map (MulAut.conj g.val).toMonoidHom)

theorem root_family_card_le_sum (K : Type) [Field K] [Finite K] (θ : Roots A)
    (hθ : ∀i,0≤θ.val i)
    (hdom : ∀i,0 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ)) :
    Nat.card (rootConjugateFamily A hd hs hp ho K θ)≤
      ∑k : Roots A,Nat.card (positiveRootOrbit A hd hs hp ho K k) := by
  classical
  have hcover (x : rootConjugateFamily A hd hs hp ho K θ) :
      ∃k : Roots A,∃y : positiveRootOrbit A hd hs hp ho K k,y.val=x.val := by
    obtain ⟨g,hg⟩ := x.property
    obtain ⟨k,u,hu⟩ := root_conjugate_eq_positive_conjugate A hd hs hp ho K θ hθ hdom g
    exact ⟨k,⟨_,⟨u,rfl⟩⟩,hu.symm.trans hg⟩
  let idx (x : rootConjugateFamily A hd hs hp ho K θ) : Roots A := Classical.choose (hcover x)
  let term (x : rootConjugateFamily A hd hs hp ho K θ) :
      positiveRootOrbit A hd hs hp ho K (idx x) := Classical.choose (Classical.choose_spec (hcover x))
  have hterm (x : rootConjugateFamily A hd hs hp ho K θ) : (term x).val=x.val :=
    Classical.choose_spec (Classical.choose_spec (hcover x))
  let enc : rootConjugateFamily A hd hs hp ho K θ→
      (k : Roots A)×positiveRootOrbit A hd hs hp ho K k := fun x=>⟨idx x,term x⟩
  have hinj : Function.Injective enc := by
    intro x y he
    apply Subtype.ext
    have hh := congrArg (fun z : (k : Roots A)×positiveRootOrbit A hd hs hp ho K k=>z.2.val) he
    change (term x).val=(term y).val at hh
    rwa [hterm,hterm] at hh
  calc
    _≤Nat.card ((k : Roots A)×positiveRootOrbit A hd hs hp ho K k) :=
      Nat.card_le_card_of_injective enc hinj
    _=_ := Nat.card_sigma

theorem root_family_card_mul_uniform_commuting_le (K : Type) [Field K] [Finite K]
    (θ : Roots A) (hθ : ∀i,0≤θ.val i)
    (hdom : ∀i,0 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ))
    (c : ℕ) (hc : ∀k : Roots A,c≤(commutingPositiveRoots A k).card) :
    Nat.card (rootConjugateFamily A hd hs hp ho K θ)*Nat.card K^c≤
      Nat.card (Roots A)*Nat.card K^Nat.card (PositiveRoot A) := by
  classical
  have hq : 0<Nat.card K := Nat.card_pos
  calc
    _≤(∑k : Roots A,Nat.card (positiveRootOrbit A hd hs hp ho K k))*Nat.card K^c :=
      Nat.mul_le_mul_right _ (root_family_card_le_sum A hd hs hp ho K θ hθ hdom)
    _=∑k : Roots A,Nat.card (positiveRootOrbit A hd hs hp ho K k)*Nat.card K^c :=
      Finset.sum_mul _ _ _
    _≤∑_k : Roots A,Nat.card K^Nat.card (PositiveRoot A) := by
      apply Finset.sum_le_sum
      intro k _
      exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq (hc k))).trans
        (positive_root_orbit_card_mul_commuting_le A hd hs hp ho K k)
    _=Nat.card (Roots A)*Nat.card K^Nat.card (PositiveRoot A) := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootFamilyCardinality
