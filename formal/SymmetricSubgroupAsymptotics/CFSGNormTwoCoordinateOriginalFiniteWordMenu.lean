import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalWordRootAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalParameterRigidity
import Mathlib.Tactic.Group

/-! One positive root label and one integral sign per simple root bound
actual ORIGINAL word values. Equal labels preserve the negative lines
as well, so positive-parameter rigidity kills the ratio conjugation.
No raw action faithfulness or generated-torus recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalFiniteWordMenu
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckColumns
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalWordRootAction CFSGNormTwoCoordinateOriginalSignedParameters
open CFSGNormTwoCoordinateOriginalSimpleParameters CFSGNormTwoCoordinateOriginalMixedA2Rigidity
open CFSGNormTwoCoordinateOriginalParameterRigidity CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGNormTwoCoordinateOriginalComplementNormalizer

private theorem ratio_preserves {G:Type*} [Group G] (S:Subgroup G) (x y:G)
    (he:S.map (MulAut.conj x).toMonoidHom=S.map (MulAut.conj y).toMonoidHom) :
    S.map (MulAut.conj (y⁻¹*x)).toMonoidHom=S := by
  apply Subgroup.map_injective (f:=(MulAut.conj y).toMonoidHom) (MulAut.conj y).injective
  rw [Subgroup.map_map]
  have hc : (MulAut.conj y).toMonoidHom.comp (MulAut.conj (y⁻¹*x)).toMonoidHom=
      (MulAut.conj x).toMonoidHom := by
    ext z
    change y*((y⁻¹*x)*z*(y⁻¹*x)⁻¹)*y⁻¹=x*z*x⁻¹
    group
  rw [hc]
  exact he

private theorem eq_of_ratio_conj_one {G:Type*} [Group G] [IsSimpleGroup G]
    (hn:¬IsMulCommutative G) (x y:G) (he:MulAut.conj (y⁻¹*x)=1) : x=y := by
  have hcenter : Subgroup.center G=⊥ := by
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hc|hc
    · exact hc
    · exact (hn (Subgroup.center_eq_top_iff.mp hc)).elim
  have hz : y⁻¹*x∈Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro a
    have hh : (y⁻¹*x)*a*(y⁻¹*x)⁻¹=a := congrArg (fun f:MulAut G=>f a) he
    have hc := congrArg (fun b=>b*(y⁻¹*x)) hh
    have hd : (y⁻¹*x)*a=a*(y⁻¹*x) := by
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hc
    exact hd.symm
  rw [hcenter] at hz
  exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hz)).symm

variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ) (hd:∀i,A i i=2)
    (hs:A.transpose=A) (hp:(rationalMatrix A).PosDef) (ho:∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K:Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

/-- The literal original projected canonical-word value range. -/
def originalWordRange [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r) :
    Set (Projective (cartan b₀ s₀) K) :=
  Set.range (fun w:List (Fin r)=>originalProjection A hd hs hp ho K i
    (elementaryWord A hd hs hp ho K w))

private theorem exists_positive_signature
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r)
    (w:List (Fin r)) (j:Fin r) : ∃b:Bool,∀a:K,
    originalWord A hd hs hp ho K i w*
      simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)*
        (originalWord A hd hs hp ho K i w)⁻¹=
      rootParameterHom A hd hs hp ho K i (wordRoot A hs hp b₀ s₀ w (s₀ j))
        (Multiplicative.ofAdd ((if b then (-1:K) else 1)*a)) := by
  obtain ⟨epsilon,hepsilon,h⟩ := originalWord_root_parameter_sign A hd hs hp ho K i w (s₀ j)
  rcases hepsilon with rfl|rfl
  · exact ⟨false,fun a=>by simpa only [rootParameterHom_simple_apply,Int.cast_one] using h a⟩
  · exact ⟨true,fun a=>by simpa only [rootParameterHom_simple_apply,Int.cast_neg,Int.cast_one] using h a⟩

private def positiveSign [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i:Fin r) (w:List (Fin r)) (j:Fin r) : Bool :=
  Classical.choose (exists_positive_signature A hd hs hp ho K i w j)

private def wordLabel [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i:Fin r) (w:List (Fin r)) : Fin r→Roots A×Bool :=
  fun j=>(wordRoot A hs hp b₀ s₀ w (s₀ j),positiveSign A hd hs hp ho K i w j)

private theorem word_eq_of_label_eq [Finite K] [Nontrivial (Fin r)]
    (p:ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r)
    (hneighbors:∀j,∃k,A j k= -1)
    (hn:¬IsMulCommutative (Projective (cartan b₀ s₀) K))
    (w v:List (Fin r))
    (he:wordLabel A hd hs hp ho K i w=wordLabel A hd hs hp ho K i v) :
    originalWord A hd hs hp ho K i w=originalWord A hd hs hp ho K i v := by
  let x := originalWord A hd hs hp ho K i w
  let y := originalWord A hd hs hp ho K i v
  let f := MulAut.conj (y⁻¹*x)
  have hroot (j:Fin r) : wordRoot A hs hp b₀ s₀ w (s₀ j)=wordRoot A hs hp b₀ s₀ v (s₀ j) :=
    congrArg Prod.fst (congrFun he j)
  have hsign (j:Fin r) : positiveSign A hd hs hp ho K i w j=positiveSign A hd hs hp ho K i v j :=
    congrArg Prod.snd (congrFun he j)
  have hpos (j:Fin r) (a:K) :
      f (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a))=
        simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a) := by
    have hw := Classical.choose_spec (exists_positive_signature A hd hs hp ho K i w j) a
    have hv := Classical.choose_spec (exists_positive_signature A hd hs hp ho K i v j) a
    change x*simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)*x⁻¹=
      rootParameterHom A hd hs hp ho K i (wordRoot A hs hp b₀ s₀ w (s₀ j))
        (Multiplicative.ofAdd ((if positiveSign A hd hs hp ho K i w j then (-1:K) else 1)*a)) at hw
    change y*simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)*y⁻¹=
      rootParameterHom A hd hs hp ho K i (wordRoot A hs hp b₀ s₀ v (s₀ j))
        (Multiplicative.ofAdd ((if positiveSign A hd hs hp ho K i v j then (-1:K) else 1)*a)) at hv
    rw [hroot j,hsign j] at hw
    have hh := hw.trans hv.symm
    change (y⁻¹*x)*simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)*(y⁻¹*x)⁻¹=_
    calc
      _=y⁻¹*(x*simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)*x⁻¹)*y := by group
      _=y⁻¹*(y*simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)*y⁻¹)*y :=
        congrArg (fun a=>y⁻¹*a*y) hh
      _=_ := by group
  have hneg (j:Fin r) :
      (originalNegativeSimpleRootGroup A hd hs hp ho K i j).map f.toMonoidHom=
        originalNegativeSimpleRootGroup A hd hs hp ho K i j := by
    apply ratio_preserves
    have hw := originalWord_negative_simple_map A hd hs hp ho K i j w
    have hv := originalWord_negative_simple_map A hd hs hp ho K i j v
    have hnr : wordRoot A hs hp b₀ s₀ w (negativeIndex A hs hp (s₀ j))=
        wordRoot A hs hp b₀ s₀ v (negativeIndex A hs hp (s₀ j)) := by
      apply Subtype.ext
      rw [wordRoot_negative_val,wordRoot_negative_val,hroot j]
    exact hw.trans ((congrArg (originalFullRootLine A hd hs hp ho K i) hnr).trans hv.symm)
  exact eq_of_ratio_conj_one hn x y
    (eq_one_of_positive_parameters_fixed A hd hs hp ho K p i hneighbors f hpos hneg)

theorem originalWordRange_card_le [Finite K] [Nontrivial (Fin r)]
    (p:ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r)
    (hneighbors:∀j,∃k,A j k= -1)
    (hn:¬IsMulCommutative (Projective (cartan b₀ s₀) K)) :
    Nat.card (originalWordRange A hd hs hp ho K i)≤(2*Nat.card (Roots A))^r := by
  let representative (x:originalWordRange A hd hs hp ho K i) : List (Fin r) :=
    Classical.choose x.property
  let encode (x:originalWordRange A hd hs hp ho K i) : Fin r→Roots A×Bool :=
    wordLabel A hd hs hp ho K i (representative x)
  have hinj : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    calc
      x.val=originalWord A hd hs hp ho K i (representative x) := (Classical.choose_spec x.property).symm
      _=originalWord A hd hs hp ho K i (representative y) :=
        word_eq_of_label_eq A hd hs hp ho K p i hneighbors hn _ _ he
      _=y.val := Classical.choose_spec y.property
  have hc := Nat.card_le_card_of_injective encode hinj
  calc
    Nat.card (originalWordRange A hd hs hp ho K i)≤Nat.card (Fin r→Roots A×Bool) := hc
    _=(2*Nat.card (Roots A))^r := by
      rw [Nat.card_fun,Nat.card_prod,Nat.card_fin]
      congr 1
      simp only [Nat.card_eq_fintype_card,Fintype.card_bool]
      omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalFiniteWordMenu
