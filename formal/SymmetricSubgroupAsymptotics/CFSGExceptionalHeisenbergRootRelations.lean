import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergRootPilot
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCommute
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootAdditive

/-! Unit-normalized Heisenberg relations from the selected integral root
configuration. A single integral sign for each complementary pair works
over every coefficient ring, so characteristic two requires no division. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergRootRelations
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup
open CFSGExceptionalHeisenbergRootPilot
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositivePairCollecting CFSGNormTwoCoordinatePositivePairCommute
variable {r m : ℕ} (A:Matrix (Fin r) (Fin r) ℤ) (hd:∀i,A i i=2)
  (hs:A.transpose=A) (hp:(rationalMatrix A).PosDef) (ho:∀i j,i≠j→A i j≤0)
  [Fintype (Roots A)] [DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
  (C:RootConfig A m)

private theorem pair_sign_exists (i:Fin m) :
    ∃ε:ℤ,(ε=1 ∨ ε= -1) ∧ ∀(K:Type)[CommRing K](a b:K),
      selectedRootElement A hd hs hp ho K (C.xRoot i).val a *
      selectedRootElement A hd hs hp ho K (C.yRoot i).val b *
      (selectedRootElement A hd hs hp ho K (C.xRoot i).val a)⁻¹ *
      (selectedRootElement A hd hs hp ho K (C.yRoot i).val b)⁻¹ =
      selectedRootElement A hd hs hp ho K C.zRoot.val ((ε:K)*(a*b)) := by
  have he : sumRoot A hs (C.xRoot i).val (C.yRoot i).val (C.paired i)=C.zRoot.val := by
    apply Subtype.ext
    exact C.sum i
  simpa only [he] using positive_pair_commutator_sign A hd hs hp ho
    (C.xRoot i).val (C.yRoot i).val (C.positive_x i) (C.positive_y i) (C.paired i)

def pairSign (i:Fin m) : ℤ := (pair_sign_exists A hd hs hp ho C i).choose

theorem pairSign_unit (i:Fin m) : pairSign A hd hs hp ho C i=1 ∨ pairSign A hd hs hp ho C i= -1 :=
  (pair_sign_exists A hd hs hp ho C i).choose_spec.1

private abbrev UnitsK (K:Type) [CommRing K] :=
  (Matrix ((coordinateBase A hd hs hp ho).support⊕Roots A)
    ((coordinateBase A hd hs hp ho).support⊕Roots A) K)ˣ

def xHom (K:Type)[CommRing K](i:Fin m) : Multiplicative K→*UnitsK A hd hs hp ho K :=
  selectedRootHom A hd hs hp ho K (C.xRoot i).val

def yHom (K:Type)[CommRing K](i:Fin m) : Multiplicative K→*UnitsK A hd hs hp ho K :=
  (selectedRootHom A hd hs hp ho K (C.yRoot i).val).comp
    (AddMonoidHom.mulLeft ((pairSign A hd hs hp ho C i:ℤ):K)).toMultiplicative

def zHom (K:Type)[CommRing K] : Multiplicative K→*UnitsK A hd hs hp ho K :=
  selectedRootHom A hd hs hp ho K C.zRoot.val

theorem x_commute (K:Type)[CommRing K](i j:Fin m)(a b:K) :
    Commute (xHom A hd hs hp ho C K i (Multiplicative.ofAdd a))
      (xHom A hd hs hp ho C K j (Multiplicative.ofAdd b)) := by
  by_cases hij:i=j
  · subst j
    exact selectedRootElement_commute A hd hs hp ho K (C.xRoot i).val a b
  · exact positive_pair_commute A hd hs hp ho K (C.xRoot i).val (C.xRoot j).val
      (C.positive_x i) (C.positive_x j) (C.within_x i j hij) a b

theorem y_commute (K:Type)[CommRing K](i j:Fin m)(a b:K) :
    Commute (yHom A hd hs hp ho C K i (Multiplicative.ofAdd a))
      (yHom A hd hs hp ho C K j (Multiplicative.ofAdd b)) := by
  by_cases hij:i=j
  · subst j
    exact selectedRootElement_commute A hd hs hp ho K (C.yRoot i).val _ _
  · exact positive_pair_commute A hd hs hp ho K (C.yRoot i).val (C.yRoot j).val
      (C.positive_y i) (C.positive_y j) (C.within_y i j hij) _ _

theorem cross_commute (K:Type)[CommRing K](i j:Fin m)(hij:i≠j)(a b:K) :
    Commute (xHom A hd hs hp ho C K i (Multiplicative.ofAdd a))
      (yHom A hd hs hp ho C K j (Multiplicative.ofAdd b)) :=
  positive_pair_commute A hd hs hp ho K (C.xRoot i).val (C.yRoot j).val
    (C.positive_x i) (C.positive_y j) (C.cross i j hij) _ _

theorem x_central (K:Type)[CommRing K](i:Fin m)(a b:K) :
    Commute (xHom A hd hs hp ho C K i (Multiplicative.ofAdd a))
      (zHom A hd hs hp ho C K (Multiplicative.ofAdd b)) :=
  positive_pair_commute A hd hs hp ho K (C.xRoot i).val C.zRoot.val
    (C.positive_x i) C.positive_z (Or.inr (C.central_x i)) _ _

theorem y_central (K:Type)[CommRing K](i:Fin m)(a b:K) :
    Commute (yHom A hd hs hp ho C K i (Multiplicative.ofAdd a))
      (zHom A hd hs hp ho C K (Multiplicative.ofAdd b)) :=
  positive_pair_commute A hd hs hp ho K (C.yRoot i).val C.zRoot.val
    (C.positive_y i) C.positive_z (Or.inr (C.central_y i)) _ _

theorem paired_commutator (K:Type)[CommRing K](i:Fin m)(a b:K) :
    xHom A hd hs hp ho C K i (Multiplicative.ofAdd a)*
      yHom A hd hs hp ho C K i (Multiplicative.ofAdd b)*
      (xHom A hd hs hp ho C K i (Multiplicative.ofAdd a))⁻¹*
      (yHom A hd hs hp ho C K i (Multiplicative.ofAdd b))⁻¹=
      zHom A hd hs hp ho C K (Multiplicative.ofAdd (a*b)) := by
  have hh := (pair_sign_exists A hd hs hp ho C i).choose_spec.2 K a
    (((pairSign A hd hs hp ho C i:ℤ):K)*b)
  have he : ((pairSign A hd hs hp ho C i:ℤ):K)*
      (a*(((pairSign A hd hs hp ho C i:ℤ):K)*b))=a*b := by
    rcases pairSign_unit A hd hs hp ho C i with h|h <;> rw [h] <;> norm_num
  change selectedRootElement A hd hs hp ho K (C.xRoot i).val a *
    selectedRootElement A hd hs hp ho K (C.yRoot i).val _ *
    (selectedRootElement A hd hs hp ho K (C.xRoot i).val a)⁻¹ *
    (selectedRootElement A hd hs hp ho K (C.yRoot i).val _)⁻¹=
    selectedRootElement A hd hs hp ho K C.zRoot.val (a*b)
  exact hh.trans (congrArg (selectedRootElement A hd hs hp ho K C.zRoot.val) he)

end SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergRootRelations
