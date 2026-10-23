import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergRootRelations
import SymmetricSubgroupAsymptotics.CFSGFiniteCommutingParameterHom
import SymmetricSubgroupAsymptotics.CFSGCentralProductCollecting
import SymmetricSubgroupAsymptotics.CFSGHeisenbergNormalFormHom

/-! The actual ordered exceptional root products realize the coordinate
Heisenberg multiplication. The Y parameters carry a minus sign; this
retains the literal cocycle +sum b_i*a'_i in characteristic two as well. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergProduct
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup CFSGExceptionalHeisenbergRootPilot
open CFSGExceptionalHeisenbergRootRelations CFSGFiniteCommutingParameterHom
open CFSGHeisenbergCoordinateGroup CFSGHeisenbergNormalFormHom
variable {r m:ℕ}(A:Matrix (Fin r) (Fin r) ℤ)(hd:∀i,A i i=2)
  (hs:A.transpose=A)(hp:(rationalMatrix A).PosDef)(ho:∀i j,i≠j→A i j≤0)
  [Fintype (Roots A)][DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced][(rootPairing A hs hp).IsIrreducible]
  (C:RootConfig A m)(K:Type)[CommRing K]
private abbrev UnitsK :=
  (Matrix ((coordinateBase A hd hs hp ho).support⊕Roots A)
    ((coordinateBase A hd hs hp ho).support⊕Roots A) K)ˣ

def yNegative (i:Fin m) : Multiplicative K→*UnitsK A hd hs hp ho K :=
  (yHom A hd hs hp ho C K i).comp (-AddMonoidHom.id K).toMultiplicative

private theorem x_pairwise : Pairwise (fun i j=>∀a b:Multiplicative K,
    Commute (xHom A hd hs hp ho C K i a) (xHom A hd hs hp ho C K j b)) := by
  intro i j _ a b
  exact x_commute A hd hs hp ho C K i j a.toAdd b.toAdd
private theorem y_pairwise : Pairwise (fun i j=>∀a b:Multiplicative K,
    Commute (yNegative A hd hs hp ho C K i a) (yNegative A hd hs hp ho C K j b)) := by
  intro i j _ a b
  exact y_commute A hd hs hp ho C K i j (-a.toAdd) (-b.toAdd)

def X : Multiplicative (Fin m→K)→*UnitsK A hd hs hp ho K :=
  parameterHom (xHom A hd hs hp ho C K) (x_pairwise A hd hs hp ho C K)
def Y : Multiplicative (Fin m→K)→*UnitsK A hd hs hp ho K :=
  parameterHom (yNegative A hd hs hp ho C K) (y_pairwise A hd hs hp ho C K)

theorem X_central (a:Fin m→K)(c:K) :
    Commute (X A hd hs hp ho C K (Multiplicative.ofAdd a))
      (zHom A hd hs hp ho C K (Multiplicative.ofAdd c)) := by
  exact (commute_parameterHom (xHom A hd hs hp ho C K) (x_pairwise A hd hs hp ho C K)
    _ (fun i t=>(x_central A hd hs hp ho C K i t.toAdd c).symm) a).symm

theorem Y_central (b:Fin m→K)(c:K) :
    Commute (Y A hd hs hp ho C K (Multiplicative.ofAdd b))
      (zHom A hd hs hp ho C K (Multiplicative.ofAdd c)) := by
  exact (commute_parameterHom (yNegative A hd hs hp ho C K) (y_pairwise A hd hs hp ho C K)
    _ (fun i t=>(y_central A hd hs hp ho C K i (-t.toAdd) c).symm) b).symm

private theorem reverse_conjugate {G:Type*}[Group G](x y z:G)
    (hz:Commute x z)(h:x*y*x⁻¹*y⁻¹=z) : y*x*y⁻¹=x*z⁻¹ := by
  have he:x*y=z*y*x := by
    calc
      _=(x*y*x⁻¹*y⁻¹)*(y*x) := by group
      _=z*(y*x) := by rw [h]
      _=z*y*x := by group
  calc
    _=z⁻¹*(z*y*x)*y⁻¹ := by group
    _=z⁻¹*(x*y)*y⁻¹ := by rw [←he]
    _=z⁻¹*x := by group
    _=x*z⁻¹ := (hz.inv_right).eq.symm

private theorem single_conjugate (i j:Fin m)(a b:K) :
    yNegative A hd hs hp ho C K i (Multiplicative.ofAdd b)*
      xHom A hd hs hp ho C K j (Multiplicative.ofAdd a)*
      (yNegative A hd hs hp ho C K i (Multiplicative.ofAdd b))⁻¹=
      xHom A hd hs hp ho C K j (Multiplicative.ofAdd a)*
        zHom A hd hs hp ho C K (Multiplicative.ofAdd (if j=i then b*a else 0)) := by
  by_cases hji:j=i
  · subst j
    rw [if_pos rfl]
    have hh:=reverse_conjugate _ _ _ (x_central A hd hs hp ho C K i a (a*(-b)))
      (paired_commutator A hd hs hp ho C K i a (-b))
    have hz:(zHom A hd hs hp ho C K (Multiplicative.ofAdd (a*(-b))))⁻¹=
        zHom A hd hs hp ho C K (Multiplicative.ofAdd (b*a)) := by
      rw [←map_inv]
      congr 1
      change -(a*(-b))=b*a
      ring
    exact hh.trans (congrArg (fun t=>xHom A hd hs hp ho C K i (Multiplicative.ofAdd a)*t) hz)
  · rw [if_neg hji]
    have hh:=cross_commute A hd hs hp ho C K j i hji a (-b)
    change _=xHom A hd hs hp ho C K j (Multiplicative.ofAdd a)*zHom A hd hs hp ho C K 1
    rw [map_one,mul_one]
    change yHom A hd hs hp ho C K i (Multiplicative.ofAdd (-b))*
      xHom A hd hs hp ho C K j (Multiplicative.ofAdd a)*
      (yHom A hd hs hp ho C K i (Multiplicative.ofAdd (-b)))⁻¹=_
    rw [hh.eq.symm]
    group

private theorem single_conjugate_X (i:Fin m)(a:Fin m→K)(b:K) :
    yNegative A hd hs hp ho C K i (Multiplicative.ofAdd b)*
      X A hd hs hp ho C K (Multiplicative.ofAdd a)*
      (yNegative A hd hs hp ho C K i (Multiplicative.ofAdd b))⁻¹=
      X A hd hs hp ho C K (Multiplicative.ofAdd a)*
        zHom A hd hs hp ho C K (Multiplicative.ofAdd (b*a i)) := by
  have hh:=CFSGCentralProductCollecting.conjugate_word
    (zHom A hd hs hp ho C K) (fun j=>xHom A hd hs hp ho C K j (Multiplicative.ofAdd (a j)))
    (yNegative A hd hs hp ho C K i (Multiplicative.ofAdd b))
    (fun j=>if j=i then b*a j else 0)
    (fun j c=>x_central A hd hs hp ho C K j (a j) c)
    (fun j=>single_conjugate A hd hs hp ho C K i j (a j) b) (List.finRange m)
  have hw:((List.finRange m).map (fun j=>xHom A hd hs hp ho C K j (Multiplicative.ofAdd (a j)))).prod=
      X A hd hs hp ho C K (Multiplicative.ofAdd a) := by
    rw [←List.ofFn_eq_map]
    exact (parameterHom_apply _ _ a).symm
  rw [hw,←Fin.sum_univ_def] at hh
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh

theorem collecting (a b:Fin m→K) :
    Y A hd hs hp ho C K (Multiplicative.ofAdd b)*X A hd hs hp ho C K (Multiplicative.ofAdd a)=
      X A hd hs hp ho C K (Multiplicative.ofAdd a)*Y A hd hs hp ho C K (Multiplicative.ofAdd b)*
        zHom A hd hs hp ho C K (Multiplicative.ofAdd (dot b a)) := by
  have hh:=CFSGCentralProductCollecting.word_conjugate
    (zHom A hd hs hp ho C K) (fun i=>yNegative A hd hs hp ho C K i (Multiplicative.ofAdd (b i)))
    (X A hd hs hp ho C K (Multiplicative.ofAdd a)) (fun i=>b i*a i)
    (fun i c=>y_central A hd hs hp ho C K i (-b i) c)
    (fun i=>single_conjugate_X A hd hs hp ho C K i a (b i)) (List.finRange m)
  have hw:((List.finRange m).map (fun i=>yNegative A hd hs hp ho C K i (Multiplicative.ofAdd (b i)))).prod=
      Y A hd hs hp ho C K (Multiplicative.ofAdd b) := by
    rw [←List.ofFn_eq_map]
    exact (parameterHom_apply _ _ b).symm
  rw [hw,←Fin.sum_univ_def] at hh
  have hc:=Y_central A hd hs hp ho C K b (dot b a)
  calc
    _=(Y A hd hs hp ho C K (Multiplicative.ofAdd b)*X A hd hs hp ho C K (Multiplicative.ofAdd a)*
        (Y A hd hs hp ho C K (Multiplicative.ofAdd b))⁻¹)*Y A hd hs hp ho C K (Multiplicative.ofAdd b) := by group
    _=(X A hd hs hp ho C K (Multiplicative.ofAdd a)*zHom A hd hs hp ho C K (Multiplicative.ofAdd (dot b a)))*
        Y A hd hs hp ho C K (Multiplicative.ofAdd b) := by rw [hh];rfl
    _=X A hd hs hp ho C K (Multiplicative.ofAdd a)*(zHom A hd hs hp ho C K (Multiplicative.ofAdd (dot b a))*
        Y A hd hs hp ho C K (Multiplicative.ofAdd b)) := by group
    _=_ := by rw [hc.eq.symm];group

def rawHom : Element K m→*UnitsK A hd hs hp ho K :=
  coordinateHom (X A hd hs hp ho C K) (Y A hd hs hp ho C K) (zHom A hd hs hp ho C K)
    (X_central A hd hs hp ho C K) (Y_central A hd hs hp ho C K) (collecting A hd hs hp ho C K)

theorem rawHom_central (c:Multiplicative K) :
    rawHom A hd hs hp ho C K (central c)=zHom A hd hs hp ho C K c :=
  coordinateHom_central _ _ _ _ _ _ c

end SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergProduct
