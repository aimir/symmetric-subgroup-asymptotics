import SymmetricSubgroupAsymptotics.CFSGTwistedDPositiveSpaceCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTailEmbedding

/-! Literal relative-root words normalize every actual maximal singular
space. The first-axis normalization and the same fixed-tail dimension
drop are used at each step; the base is the checked anisotropic-plane
argument in natural rank two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDMaximalSpaceOrbit
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDFixedTailLinear CFSGTwistedDSingularTailDimension
open CFSGTwistedDSingularDimensionBound CFSGTwistedDRelativeTailEmbedding
open CFSGTwistedDMaximalSingularDimension CFSGTwistedDPositiveSpaceCoordinates
open CFSGTwistedA2FixedField

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem tail_fixed_action (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (v : fixedSpace (n + 1) q) :
    tailLinear n q (fixedLinearHom (n + 1) q (tailRelativeHom n q g) v) =
      fixedLinearHom n q g (tailLinear n q v) := by
  apply Subtype.ext
  exact tail_action n q g v.val

theorem negativeHead_fixed_action (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (v : fixedSpace (n + 1) q) :
    negativeHead n q (fixedLinearHom (n + 1) q (tailRelativeHom n q g) v) =
      negativeHead n q v := by
  apply Subtype.ext
  exact head_negative n q g v.val

theorem positive_of_head_tail (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (n + 1) q) (hh : negativeHead n q v = 0)
    (ht : tailLinear n q v ∈ positiveSpace n q) :
    v ∈ positiveSpace (n + 1) q := by
  rw [mem_positiveSpace_iff] at ht ⊢
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrArg (fun a : fixedField q => (a : q.Extension 2)) hh
  · exact ht j

theorem exists_normalize_full_rank (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q))
    (hs : ∀ v ∈ P, fixedQuadraticForm n q v = 0)
    (hd : Module.finrank (fixedField q) P = n + 1) :
    ∃ g : relativeRootGroup n q,
      P.map (fixedLinearHom n q g).toLinearMap = positiveSpace n q := by
  induction n with
  | zero =>
    have hP : P ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
    obtain ⟨g, hu, hsing⟩ := exists_normalize_subspace 0 q P hs hP
    let A := P.map (fixedLinearHom 0 q g).toLinearMap
    have hle : A ≤ positiveSpace 0 q := by
      apply (base_singular_axis_bound q A hsing hu).trans
      apply Submodule.span_le.mpr
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst v
      change firstAxis 0 q ∈ positiveSpace 0 q
      rw [mem_positiveSpace_iff]
      intro i
      change (Pi.single (Sum.inl (0 : Fin 2)) (1 : q.Extension 2) :
        Index 2 → q.Extension 2) (Sum.inr i) = 0
      simp only [Pi.single_apply, Sum.inr_ne_inl, if_false]
    refine ⟨g, Submodule.eq_of_le_of_finrank_le hle ?_⟩
    rw [positiveSpace_finrank, (fixedLinearHom 0 q g).finrank_map_eq, hd]
  | succ n ih =>
    have hP : P ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
    obtain ⟨g, hu, hsing⟩ := exists_normalize_subspace (n + 1) q P hs hP
    let A := P.map (fixedLinearHom (n + 1) q g).toLinearMap
    have huA : fixedFirst n q ∈ A := hu
    have hA : Module.finrank (fixedField q) A = n + 2 :=
      ((fixedLinearHom (n + 1) q g).finrank_map_eq P).trans hd
    let T := A.map (tailLinear n q)
    have hTsing : ∀ v ∈ T, fixedQuadraticForm n q v = 0 :=
      tail_singular n q A hsing huA
    have hTdim : Module.finrank (fixedField q) T = n + 1 := by
      have he := tail_finrank n q A hsing huA
      change Module.finrank (fixedField q) T + 1 = Module.finrank (fixedField q) A at he
      omega
    obtain ⟨h, hh⟩ := ih T hTsing hTdim
    let t := tailRelativeHom n q h
    let C := A.map (fixedLinearHom (n + 1) q t).toLinearMap
    have hCdim : Module.finrank (fixedField q) C = n + 2 :=
      ((fixedLinearHom (n + 1) q t).finrank_map_eq A).trans hA
    have hle : C ≤ positiveSpace (n + 1) q := by
      rintro v ⟨x, hx, rfl⟩
      apply positive_of_head_tail n q
      · change negativeHead n q
          (fixedLinearHom (n + 1) q (tailRelativeHom n q h) x) = 0
        rw [negativeHead_fixed_action]
        exact negativeHead_zero n q A hsing huA x hx
      · change tailLinear n q
          (fixedLinearHom (n + 1) q (tailRelativeHom n q h) x) ∈ positiveSpace n q
        rw [tail_fixed_action]
        have hm : fixedLinearHom n q h (tailLinear n q x) ∈
            T.map (fixedLinearHom n q h).toLinearMap :=
          ⟨tailLinear n q x, ⟨x, hx, rfl⟩, rfl⟩
        rw [hh] at hm
        exact hm
    have hC : C = positiveSpace (n + 1) q :=
      Submodule.eq_of_le_of_finrank_le hle (by rw [positiveSpace_finrank, hCdim])
    refine ⟨t * g, ?_⟩
    have hcomp : (fixedLinearHom (n + 1) q (t * g)).toLinearMap =
        (fixedLinearHom (n + 1) q t).toLinearMap.comp
          (fixedLinearHom (n + 1) q g).toLinearMap := by
      rw [map_mul]
      rfl
    rw [hcomp, Submodule.map_comp]
    exact hC

theorem exists_normalize_maximal (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q))
    (hP : CFSGQuadraticMaximalSingularGallery.MaximalSingular (fixedQuadraticForm n q) P) :
    ∃ g : relativeRootGroup n q,
      P.map (fixedLinearHom n q g).toLinearMap = positiveSpace n q :=
  exists_normalize_full_rank n q P hP.1 (maximalSingular_finrank n q P hP)

end SymmetricSubgroupAsymptotics.CFSGTwistedDMaximalSpaceOrbit
