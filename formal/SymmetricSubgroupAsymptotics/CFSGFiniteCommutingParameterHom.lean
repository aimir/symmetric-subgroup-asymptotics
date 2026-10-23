import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.BigOperators.Fin

/-! Finite commuting additive root-parameter families, with an explicit
ordered-word formula. This is a universal-property construction, not a
root-group identification assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteCommutingParameterHom
variable {K G:Type*}[AddCommGroup K][Group G]{m:ℕ}
variable (f:Fin m→Multiplicative K→*G)
  (hcomm:Pairwise (fun i j=>∀a b,Commute (f i a) (f j b)))

def parameterHom : Multiplicative (Fin m→K)→*G :=
  (MonoidHom.noncommPiCoprod f hcomm).comp
    (MulEquiv.piMultiplicative (fun _:Fin m=>K)).toMonoidHom

theorem parameterHom_apply (v:Fin m→K) :
    parameterHom f hcomm (Multiplicative.ofAdd v)=
      (List.ofFn (fun i=>f i (Multiplicative.ofAdd (v i)))).prod := by
  change Finset.univ.noncommProd (fun i=>f i (Multiplicative.ofAdd (v i)))
    (fun i _ j _ hij=>hcomm hij (Multiplicative.ofAdd (v i)) (Multiplicative.ofAdd (v j)))=_
  rw [←List.toFinset_finRange m,Finset.noncommProd_toFinset _ _ _ (List.nodup_finRange m)]
  rw [←List.ofFn_eq_map]

theorem parameterHom_single (i:Fin m)(a:K) :
    parameterHom f hcomm (Multiplicative.ofAdd (Pi.single i a))=f i (Multiplicative.ofAdd a) := by
  have he : (MulEquiv.piMultiplicative (fun _:Fin m=>K))
      (Multiplicative.ofAdd (Pi.single i a))=Pi.mulSingle i (Multiplicative.ofAdd a) := by
    ext j
    by_cases hj:j=i
    · subst j
      change Multiplicative.ofAdd ((Pi.single i a:Fin m→K) i)=
        (Pi.mulSingle i (Multiplicative.ofAdd a):Fin m→Multiplicative K) i
      rw [Pi.single_eq_same,Pi.mulSingle_eq_same]
    · change Multiplicative.ofAdd ((Pi.single i a:Fin m→K) j)=
        (Pi.mulSingle i (Multiplicative.ofAdd a):Fin m→Multiplicative K) j
      rw [Pi.single_eq_of_ne hj,Pi.mulSingle_eq_of_ne hj]
      rfl
  change MonoidHom.noncommPiCoprod f hcomm
    ((MulEquiv.piMultiplicative (fun _:Fin m=>K)) (Multiplicative.ofAdd (Pi.single i a)))=_
  rw [he,MonoidHom.noncommPiCoprod_mulSingle]

theorem commute_parameterHom (g:G) (hg:∀i a,Commute g (f i a)) (v:Fin m→K) :
    Commute g (parameterHom f hcomm (Multiplicative.ofAdd v)) := by
  exact MonoidHom.commute_noncommPiCoprod (hcomm:=hcomm) f hg _

end SymmetricSubgroupAsymptotics.CFSGFiniteCommutingParameterHom
