import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalChainStar
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarReverseRows
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSignedSimple
import SymmetricSubgroupAsymptotics.CFSGSLAdjacentRootParameterAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamily

/-! Adjacent elementary rows of the chain star are realized by literal
original-group words. Combined with the proved positive-chart injection,
this gives the field-power lower bound on EVERY proper original index.
There is no row-action, source-kernel or SL-lifting hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalChainStarRows
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGSerreQuadraticMatrix CFSGNormTwoGeckIntegralRealization
open CFSGExceptionalChainStarData CFSGNormTwoCoordinateOriginalChainStar
open CFSGNormTwoCoordinateRootStarHom CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinatePositiveQuotientInjectivity CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoCoordinateOriginalSignedSimple CFSGNormTwoCoordinateChainStarForwardRows
open CFSGNormTwoCoordinateChainStarReverseRows CFSGTypeAElementaryMatrices
variable {r n : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] (C : ChainStar A n)
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordUnits := (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ
variable (i₀ : Fin r)

private theorem project_row [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (g : ElementaryGroup A hd hs hp ho K)
    (E : Matrix.SpecialLinearGroup (Fin (n+1)) K)
    (hraw : ∀v:Fin (n+1)→K,(g:CoordUnits A hd hs hp ho K)*rawHom A hd hs hp ho K C.root C.pair (Multiplicative.ofAdd v)*
      (g:CoordUnits A hd hs hp ho K)⁻¹=rawHom A hd hs hp ho K C.root C.pair (Multiplicative.ofAdd (E.toLin' v))) :
    ∀v:Fin (n+1)→K,originalProjection A hd hs hp ho K i₀ g*
      originalStarHom A hd hs hp ho K C i₀ (Multiplicative.ofAdd v)=
      originalStarHom A hd hs hp ho K C i₀ (Multiplicative.ofAdd (E.toLin' v))*
        originalProjection A hd hs hp ho K i₀ g := by
  let z := (positiveInclusion A hd hs hp ho K).comp (positiveStarHom A hd hs hp ho K C)
  intro v
  change originalProjection A hd hs hp ho K i₀ g*originalProjection A hd hs hp ho K i₀ (z (Multiplicative.ofAdd v))=
    originalProjection A hd hs hp ho K i₀ (z (Multiplicative.ofAdd (E.toLin' v)))*originalProjection A hd hs hp ho K i₀ g
  rw [←map_mul,←map_mul]
  apply congrArg (originalProjection A hd hs hp ho K i₀)
  apply Subtype.ext
  change (g:CoordUnits A hd hs hp ho K)*rawHom A hd hs hp ho K C.root C.pair (Multiplicative.ofAdd v)=
    rawHom A hd hs hp ho K C.root C.pair (Multiplicative.ofAdd (E.toLin' v))*(g:CoordUnits A hd hs hp ho K)
  exact (mul_inv_eq_iff_eq_mul).mp (hraw v)

theorem adjacent_rows [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin (n+1)) (hij:i≠j)
    (hadj : i.val+1=j.val ∨ j.val+1=i.val) (a:K) :
    ∃g:Projective (cartan b₀ s₀) K,∀v:Fin (n+1)→K,
      g*originalStarHom A hd hs hp ho K C i₀ (Multiplicative.ofAdd v)=
        originalStarHom A hd hs hp ho K C i₀
          (Multiplicative.ofAdd ((elementary hij a).toLin' v))*g := by
  rcases hadj with hadj|hadj
  · have hindices : ∃k:Fin n,i=k.castSucc ∧ j=k.succ := by
      refine ⟨⟨i.val,by omega⟩,Fin.ext rfl,Fin.ext ?_⟩
      simpa only [Fin.val_succ] using hadj.symm
    obtain ⟨k,hi,hj⟩ := hindices
    subst i
    subst j
    obtain ⟨t,ht⟩ := reverse_row A hd hs hp ho K C k a
    let w := elementaryWord A hd hs hp ho K [C.step k]
    let u := elementarySimpleHom A hd hs hp ho K false (C.step k) (Multiplicative.ofAdd t)
    let g := w*u*w⁻¹
    refine ⟨originalProjection A hd hs hp ho K i₀ g,?_⟩
    apply project_row A hd hs hp ho K C i₀ g (elementary hij a)
    intro v
    have hw : (w:CoordUnits A hd hs hp ho K)=canonicalWeyl D K (C.step k) := by
      change canonicalWeyl D K (C.step k)*1=canonicalWeyl D K (C.step k)
      exact mul_one _
    change ((w:CoordUnits A hd hs hp ho K)*canonicalRoot D K false (C.step k) t*(w:CoordUnits A hd hs hp ho K)⁻¹)*
      rawHom A hd hs hp ho K C.root C.pair (Multiplicative.ofAdd v)*
      ((w:CoordUnits A hd hs hp ho K)*canonicalRoot D K false (C.step k) t*(w:CoordUnits A hd hs hp ho K)⁻¹)⁻¹=_
    rw [hw]
    exact ht v
  · have hindices : ∃k:Fin n,i=k.succ ∧ j=k.castSucc := by
      refine ⟨⟨j.val,by omega⟩,Fin.ext ?_,Fin.ext rfl⟩
      simpa only [Fin.val_succ] using hadj.symm
    obtain ⟨k,hi,hj⟩ := hindices
    subst i
    subst j
    obtain ⟨t,ht⟩ := forward_row A hd hs hp ho K C k a
    let g := elementarySimpleHom A hd hs hp ho K false (C.step k) (Multiplicative.ofAdd t)
    refine ⟨originalProjection A hd hs hp ho K i₀ g,?_⟩
    apply project_row A hd hs hp ho K C i₀ g (elementary hij a)
    intro v
    exact ht v

include C i₀ in
theorem field_power_le_proper_index [Finite K] [Nontrivial (Fin r)]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hn:0<n)
    (H : Subgroup (Projective (cartan b₀ s₀) K)) (hH:H≠⊤) : Nat.card K^(n+1)≤H.index := by
  letI : Finite (Projective (cartan b₀ s₀) K) :=
    CFSGNormTwoCoordinateOriginalRootFamily.original_projective_finite A hd hs hp ho K i₀
  let b : Fin (n+1) := ⟨0,by omega⟩
  let c : Fin (n+1) := ⟨1,by omega⟩
  have hbc : b≠c := by
    intro he
    have hv := congrArg Fin.val he
    change (0:ℕ)=1 at hv
    omega
  exact CFSGSLAdjacentRootParameterAction.field_power_le_proper_index
    (originalStarHom A hd hs hp ho K C i₀) b c hbc
    (originalStarHom_injective A hd hs hp ho K C p i₀)
    (adjacent_rows A hd hs hp ho K C i₀) H hH

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalChainStarRows
