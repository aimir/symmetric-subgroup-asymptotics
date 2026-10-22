import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroup

/-! Actual Weyl-word conjugation permutes the original lattice-indexed
root subgroups by the SAME original reflection word. No arbitrary action
chart or matrix-to-lattice faithfulness assumption is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWeylAction
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSerreQuadraticWordRootTransport CFSGNormTwoCoordinateRootSubgroup
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

omit [(rootPairing A hs hp).IsReduced] in
private theorem canonicalWord_append (K : Type) [Field K] (u w : List (Fin r)) :
    canonicalWord D K (u++w)=canonicalWord D K u*canonicalWord D K w := by
  induction u with
  | nil=>simp only [List.nil_append,canonicalWord,one_mul]
  | cons i u ih=>rw [List.cons_append,canonicalWord,ih,canonicalWord,mul_assoc]

theorem wordRootSubgroup_map_conjugate (K : Type) [Field K]
    (u w : List (Fin r)) (i : Fin r) :
    (wordRootSubgroup A hd hs hp ho K w i).map
      (MulAut.conj (canonicalWord D K u)).toMonoidHom=
        wordRootSubgroup A hd hs hp ho K (u++w) i := by
  have he : ∀a : K,(MulAut.conj (canonicalWord D K u)) (rootWord D K w true i a)=
      rootWord D K (u++w) true i a := by
    intro a
    change canonicalWord D K u*(canonicalWord D K w*canonicalRoot D K true i a*
      (canonicalWord D K w)⁻¹)*(canonicalWord D K u)⁻¹=
        canonicalWord D K (u++w)*canonicalRoot D K true i a*(canonicalWord D K (u++w))⁻¹
    rw [canonicalWord_append]
    group
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨a,rfl⟩ := (mem_wordRootSubgroup_iff A hd hs hp ho K w i y).mp hy
    exact (mem_wordRootSubgroup_iff A hd hs hp ho K (u++w) i _).mpr ⟨a,(he a).symm⟩
  · intro hx
    obtain ⟨a,rfl⟩ := (mem_wordRootSubgroup_iff A hd hs hp ho K (u++w) i x).mp hx
    exact ⟨rootWord D K w true i a,
      (mem_wordRootSubgroup_iff A hd hs hp ho K w i _).mpr ⟨a,rfl⟩,he a⟩

theorem rootSubgroup_map_word (K : Type) [Field K] (u : List (Fin r)) (k : Roots A) :
    (rootSubgroup A hd hs hp ho K k).map (MulAut.conj (canonicalWord D K u)).toMonoidHom=
      rootSubgroup A hd hs hp ho K (wordRoot A hs hp b₀ s₀ u k) := by
  let p := rootWitness A hd hs hp ho k
  have hdegree : (wordRoot A hs hp b₀ s₀ u k).val=
      wordLinear A hs hp b₀ s₀ (u++p.val.1) (-(s₀ p.val.2:Roots A).val) := by
    calc
      _=wordLinear A hs hp b₀ s₀ u k.val := (wordLinear_root A hs hp b₀ s₀ u k).symm
      _=wordLinear A hs hp b₀ s₀ u
          (wordLinear A hs hp b₀ s₀ p.val.1 (-(s₀ p.val.2:Roots A).val)) :=
        congrArg (wordLinear A hs hp b₀ s₀ u) p.property
      _=_ := by rw [wordLinear_append];rfl
  rw [rootSubgroup_eq_word A hd hs hp ho K _ (u++p.val.1) p.val.2 hdegree]
  change (wordRootSubgroup A hd hs hp ho K p.val.1 p.val.2).map _= _
  exact wordRootSubgroup_map_conjugate A hd hs hp ho K u p.val.1 p.val.2

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWeylAction
