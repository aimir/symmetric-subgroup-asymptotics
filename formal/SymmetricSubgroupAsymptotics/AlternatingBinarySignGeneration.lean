import SymmetricSubgroupAsymptotics.FourBlockBinarySignGeneration
import SymmetricSubgroupAsymptotics.TernaryFourPairingCocycles

/-! Even and full sign generation under the actual alternating block
action. The original two three-cycles generate the complement. Their
orbits give every coordinate translation and the required sign space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.AlternatingBinarySignGeneration

open SemidirectProduct BinarySignTernaryLinear FourBlockBinarySignSpaces
open FourBlockBinarySignGeneration TernaryFourPairingCocycles

def reach : Fin 4 → A4 :=
  ![1,alternatingFirst,alternatingFirst^2,alternatingSecond*alternatingFirst^2]

theorem reach_zero : ∀ i : Fin 4, reach i • (0 : Fin 4) = i := by decide +kernel

theorem transitive : ∀ i : Fin 4, ∃ g : A4, g • (0 : Fin 4) = i :=
  fun i => ⟨reach i,reach_zero i⟩

theorem sign_span (even : Bool) (S : Submodule (ZMod 2) BinaryVector)
    (h : ∀ g : A4, (fun i => (signSeed (R := A4) even).1 (g⁻¹ • i)) ∈ S)
    (v : (space (R := A4) even).toSubmodule) : v.1 ∈ S := by
  cases even
  · have hsingle (i : Fin 4) : (Pi.single i 1 : BinaryVector) ∈ S := by
      have hi := h (reach i)
      have he : (fun j => (signSeed (R := A4) false).1 ((reach i)⁻¹ • j)) =
          (Pi.single i 1 : BinaryVector) :=
        (by decide +kernel : ∀ i : Fin 4,
          (fun j => (signSeed (R := A4) false).1 ((reach i)⁻¹ • j)) =
            (Pi.single i 1 : BinaryVector)) i
      rwa [he] at hi
    have he : (∑ i : Fin 4, v.1 i • (Pi.single i 1 : BinaryVector)) = v.1 := by
      calc
        _ = ∑ i, Pi.single i (v.1 i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Pi.single_smul]
          simp
        _ = v.1 := LinearMap.sum_single_apply (fun _ : Fin 4 => ZMod 2) v.1
    rw [← he]
    exact S.sum_mem fun i _ => S.smul_mem _ (hsingle i)
  · have hp (i : Fin 4) : pair 0 i ∈ S := by
      fin_cases i
      · change pair 0 0 ∈ S
        have he : pair 0 0 = 0 := by decide +kernel
        rw [he]
        exact S.zero_mem
      · exact h 1
      · have he : (fun j => (signSeed (R := A4) true).1 (alternatingSecond⁻¹ • j)) =
          pair 0 2 := by decide +kernel
        exact he ▸ h alternatingSecond
      · have he : (fun j => (signSeed (R := A4) true).1 ((alternatingSecond^2)⁻¹ • j)) =
          pair 0 3 := by decide +kernel
        exact he ▸ h (alternatingSecond^2)
    have hsum : ∑ i : Fin 4, v.1 i = 0 := v.2
    have he : (∑ i : Fin 4, v.1 i • pair 0 i) = v.1 := by
      simp only [pair,smul_add,Finset.sum_add_distrib,← Finset.sum_smul,hsum,
        zero_smul,zero_add]
      calc
        _ = ∑ i, Pi.single i (v.1 i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Pi.single_smul]
          simp
        _ = v.1 := LinearMap.sum_single_apply (fun _ : Fin 4 => ZMod 2) v.1
    rw [← he]
    exact S.sum_mem fun i _ => S.smul_mem _ (hp i)

theorem sign_model_eq_top (even : Bool)
    (K : Subgroup (SignModel (space (R := A4) even)))
    (hseed : inl (Multiplicative.ofAdd (signSeed (R := A4) even)) ∈ K)
    (hblocks : ∀ g : A4, inr g ∈ K) : K = ⊤ := by
  let E := space (R := A4) even
  let rho := CyclicOrbitBinarySignNormalGenerators.linearAction E
  let S := translationSubmodule rho K
  let U : Submodule (ZMod 2) BinaryVector := S.map E.toSubmodule.subtype
  have horbit (g : A4) : (fun i => (signSeed (R := A4) even).1 (g⁻¹ • i)) ∈ U := by
    have hs : signSeed (R := A4) even ∈ S := hseed
    have hg := translation_conjugate rho K (inr g) (hblocks g) _ hs
    exact ⟨rho g (signSeed (R := A4) even),hg,rfl⟩
  apply eq_top_of_translations rho K ?_ hblocks
  apply top_unique
  intro v _
  have hv : v.1 ∈ U := sign_span even U horbit v
  obtain ⟨w,hw,he⟩ := hv
  have hwe : w = v := Subtype.ext he
  rwa [hwe] at hw

abbrev Model (even : Bool) := BinarySignTernaryAffineSocles.Model (space (R := A4) even)
abbrev action (even : Bool) := BinarySignTernaryPointAction.action (space (R := A4) even)

def lifts (even : Bool) : Fin 4 → Model even :=
  ![inl (Multiplicative.ofAdd (Pi.single 0 1)),
    inr (inl (Multiplicative.ofAdd (signSeed even))),
    inr (inr alternatingFirst),inr (inr alternatingSecond)]

theorem model_eq_top (even : Bool) (K : Subgroup (Model even))
    (h : ∀ i : Fin 4, lifts even i ∈ K) : K = ⊤ := by
  let E := space (R := A4) even
  let rho := linearHom E
  have hblocks : ∀ g : A4, inr (inr g) ∈ K := by
    let B : Subgroup A4 := K.comap (inr.comp inr)
    have hB : (⊤ : Subgroup A4) ≤ B := by
      rw [← alternating_pair_generated]
      apply (Subgroup.closure_le _).mpr
      intro g hg
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact h 2
      · exact h 3
    exact fun g => hB (Subgroup.mem_top _)
  have hsigns : ∀ g : SignModel E, inr g ∈ K := by
    have ht : K.comap inr = ⊤ := sign_model_eq_top even (K.comap inr) (h 1) hblocks
    intro g
    have hg : g ∈ K.comap inr := by rw [ht]; exact Subgroup.mem_top _
    exact hg
  apply eq_top_of_translations rho K ?_ hsigns
  let S := translationSubmodule rho K
  have hsingle (i : Fin 4) : (Pi.single i 1 : Vector) ∈ S := by
    have hs : (Pi.single 0 1 : Vector) ∈ S := h 0
    have hg := translation_conjugate rho K (inr (inr (reach i))) (hblocks (reach i)) _ hs
    have he : rho (inr (reach i)) (Pi.single 0 1) = Pi.single i 1 := by
      rw [BinarySignTernaryLinear.single_inr,reach_zero]
    exact he ▸ hg
  apply top_unique
  intro v _
  have he : (∑ i : Fin 4, v i • (Pi.single i 1 : Vector)) = v := by
    calc
      _ = ∑ i, Pi.single i (v i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Pi.single_smul]
        simp
      _ = v := LinearMap.sum_single_apply (fun _ : Fin 4 => ZMod 3) v
  rw [← he]
  exact S.sum_mem fun i _ => S.smul_mem _ (hsingle i)

theorem range_eq (even : Bool) (generators : Fin 4 → Equiv.Perm (Fin 12))
    (hbind : ∀ i, action even (lifts even i) = generators i) :
    (action even).range = Subgroup.closure (Set.range generators) := by
  let T := Subgroup.closure (Set.range generators)
  let K := T.comap (action even)
  have hK : K = ⊤ := model_eq_top even K (by
    intro i
    change action even (lifts even i) ∈ T
    rw [hbind]
    exact Subgroup.subset_closure (Set.mem_range_self i))
  apply le_antisymm
  · rintro _ ⟨g,rfl⟩
    have hg : g ∈ K := by rw [hK]; exact Subgroup.mem_top _
    exact hg
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨lifts even i,hbind i⟩

end SymmetricSubgroupAsymptotics.AlternatingBinarySignGeneration

end
