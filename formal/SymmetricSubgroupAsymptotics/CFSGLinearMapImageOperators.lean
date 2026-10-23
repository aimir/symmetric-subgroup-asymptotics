import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range

/-! Operators on an actual linear-map range. Intertwining, rather than
injectivity of the source map, supplies both range invariance and zero
products on that range. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGLinearMapImageOperators
variable {K S V : Type*} [CommRing K]
    [AddCommGroup S] [Module K S] [AddCommGroup V] [Module K V]

def rangeOperator (F : S →ₗ[K] V) (P : Module.End K S) (T : Module.End K V)
    (h : ∀ x, F (P x)=T (F x)) : Module.End K F.range where
  toFun x:=⟨T x.val, by
    obtain ⟨y, hy⟩:=x.property
    exact ⟨P y, by rw [h, hy]⟩⟩
  map_add' x y:=Subtype.ext (T.map_add x.val y.val)
  map_smul' c x:=Subtype.ext (T.map_smul c x.val)

theorem rangeOperator_rangeRestrict (F : S →ₗ[K] V) (P : Module.End K S)
    (T : Module.End K V) (h : ∀ x, F (P x)=T (F x)) (x : S) :
    rangeOperator F P T h (F.rangeRestrict x)=F.rangeRestrict (P x) :=
  Subtype.ext (h x).symm

theorem rangeOperator_mul_eq_zero (F : S →ₗ[K] V) (P Q : Module.End K S)
    (T U : Module.End K V) (hP : ∀ x, F (P x)=T (F x)) (hQ : ∀ x, F (Q x)=U (F x))
    (hzero : ∀ x, F (P (Q x))=0) :
    rangeOperator F P T hP*rangeOperator F Q U hQ=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩:=x.property
  change T (U x.val)=0
  rw [←hy,←hQ,←hP]
  exact hzero y

end SymmetricSubgroupAsymptotics.CFSGLinearMapImageOperators
