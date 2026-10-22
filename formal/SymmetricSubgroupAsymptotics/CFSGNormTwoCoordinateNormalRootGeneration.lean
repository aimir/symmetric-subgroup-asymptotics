import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalSimpleRootGeneration
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHighestRootUnitCharacter
import SymmetricSubgroupAsymptotics.CFSGFieldRootNormalSaturation

/-! Actual normal-root generation: a full selected root line normally
generates the canonical matrix group. A single NONZERO dominant-root
parameter already suffices, by its proved full torus-unit character. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalRootGeneration
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckIntegralWord CFSGSerreQuadraticWordRootTransport
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateNormalSimpleRootGeneration
open CFSGNormTwoCoordinateRootTorusConjugation CFSGNormTwoCoordinateHighestRootUnitCharacter
open CFSGNormTwoGeckSelfRootConjugation CFSGFieldRootNormalSaturation
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem normal_eq_top_of_selected_root_line (K : Type) [Field K]
    (N : Subgroup (ElementaryGroup A hd hs hp ho K)) [N.Normal] (k : Roots A)
    (hline : ∀a : K,elementarySelectedRootHom A hd hs hp ho K k (Multiplicative.ofAdd a)∈N) : N=⊤ := by
  let p := rootWitness A hd hs hp ho k
  let w := elementaryWord A hd hs hp ho K p.val.1
  have hneg : ∀a : K,canonicalElementaryRoot D K true p.val.2 a∈N := by
    intro a
    have hn := (inferInstance : N.Normal).conj_mem
      (elementarySelectedRootHom A hd hs hp ho K k (Multiplicative.ofAdd a)) (hline a) w⁻¹
    have he : w⁻¹*elementarySelectedRootHom A hd hs hp ho K k (Multiplicative.ofAdd a)*
        (w⁻¹)⁻¹=canonicalElementaryRoot D K true p.val.2 a := by
      rw [inv_inv]
      apply Subtype.ext
      change (wordUnit A hs hp b₀ s₀ K p.val.1)⁻¹*
        rootWord D K p.val.1 true p.val.2 a*wordUnit A hs hp b₀ s₀ K p.val.1=
          canonicalRoot D K true p.val.2 a
      rw [rootWord,word_eq_canonicalWord]
      group
    rw [he] at hn
    exact hn
  have hpos : ∀a : K,canonicalElementaryRoot D K false p.val.2 a∈N := by
    intro a
    let v := elementaryWord A hd hs hp ho K [p.val.2]
    have hv : v.val=canonicalWeyl D K p.val.2 := by
      change wordUnit A hs hp b₀ s₀ K [p.val.2]=_
      simp only [wordUnit,mul_one]
    have hn := (inferInstance : N.Normal).conj_mem
      (canonicalElementaryRoot D K true p.val.2 (-a)) (hneg (-a)) v⁻¹
    have he : v⁻¹*canonicalElementaryRoot D K true p.val.2 (-a)*(v⁻¹)⁻¹=
        canonicalElementaryRoot D K false p.val.2 a := by
      rw [inv_inv]
      apply Subtype.ext
      change v.val⁻¹*canonicalRoot D K true p.val.2 (-a)*v.val=
        canonicalRoot D K false p.val.2 a
      rw [hv,←self_root_word A hs hp b₀ s₀ K p.val.2 a]
      group
    rw [he] at hn
    exact hn
  exact normal_eq_top_of_simple_root_line A hd hs hp ho K N p.val.2 hpos

theorem normal_eq_top_of_nonzero_dominant_root (K : Type) [Field K] [Nontrivial (Fin r)]
    (N : Subgroup (ElementaryGroup A hd hs hp ho K)) [N.Normal] (θ : Roots A)
    (hθ : ∀i,0≤θ.val i)
    (hdom : ∀i,0 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ))
    (a : K) (ha : a≠0)
    (hNa : elementarySelectedRootHom A hd hs hp ho K θ (Multiplicative.ofAdd a)∈N) : N=⊤ := by
  obtain ⟨i,hpair⟩ := dominant_root_has_unit_simple_pairing A hd hs hp ho θ hθ hdom
  have hact : ∀t : Kˣ,∀b : K,
      elementaryTorus A hd hs hp ho K i t*
        elementarySelectedRootHom A hd hs hp ho K θ (Multiplicative.ofAdd b)*
        (elementaryTorus A hd hs hp ho K i t)⁻¹=
      elementarySelectedRootHom A hd hs hp ho K θ (Multiplicative.ofAdd (b*(t:K))) := by
    intro t b
    apply Subtype.ext
    simpa only [hpair,zpow_one] using torus_conjugate_selected_root A hd hs hp ho K i t θ b
  have hline := root_range_le_normal_of_nonzero (elementarySelectedRootHom A hd hs hp ho K θ)
    (elementaryTorus A hd hs hp ho K i) hact N a ha hNa
  exact normal_eq_top_of_selected_root_line A hd hs hp ho K N θ (fun b=>hline ⟨Multiplicative.ofAdd b,rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalRootGeneration
