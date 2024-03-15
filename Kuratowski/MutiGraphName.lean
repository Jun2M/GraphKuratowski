import Mathlib
import Wagner.Sym2
import Wagner.NotSure

open Classical

structure MultiGraphDissociatedNames (αᵥ αₑ : Type*) where
  V : Set αᵥ
  inc : αₑ → Option (Sym2 αᵥ)
  E : Set αₑ := { e | inc e ≠ none}
  domain_inc : E = { e | (inc e).isSome }
  range_inc : ∀ (e : αₑ) (he : (inc e).isSome ), ↑((inc e).get he) ⊆ V


namespace MultiGraphDissociatedNames

variable {αᵥ αₑ : Type*}


noncomputable def removeVertex (G : MultiGraphDissociatedNames αᵥ αₑ) (v : αᵥ) (_ : v ∈ G.V) :
  MultiGraphDissociatedNames αᵥ αₑ where
  V := G.V \ {v}
  inc := λ e =>
    if ((G.inc e).map (v ∈ ·)).getD false then
      none
    else
      G.inc e

  domain_inc := rfl
  range_inc := by
    simp
    intro e he w hw
    simp_all
    by_cases h : Option.getD (Option.map (fun x ↦ v ∈ x) (G.inc e)) False
    <;> simp [h] at he hw

    · refine ⟨ G.range_inc e he hw, ?_ ⟩
      rintro rfl
      by_cases h' : Option.map (fun x ↦ w ∈ x) (G.inc e) = some (true = true)
      · simp [h'] at h
      · simp_all
    done

noncomputable def removeEdge (G : MultiGraphDissociatedNames αᵥ αₑ) (e : αₑ) (_ : e ∈ G.E) :
  MultiGraphDissociatedNames αᵥ αₑ where
  V := G.V
  inc := λ e' =>
    if e' = e then
      none
    else
      G.inc e'

  domain_inc := rfl

  range_inc := by
    simp
    intro e' he' v hv
    simp_all
    by_cases h : e' = e
    <;> simp [h] at he' hv
    · exact G.range_inc e' he' hv
    done

noncomputable def vertexMerge (G : MultiGraphDissociatedNames αᵥ αₑ) (v w : αᵥ) (hdistinct : v ≠ w)
  (_ : v ∈ G.V) (_ : w ∈ G.V) :
  MultiGraphDissociatedNames αᵥ αₑ where
  V := G.V \ {w}
  inc := λ e =>
    (G.inc e).map (·.map (λ x => if x = w then v else x))

  domain_inc := rfl

  range_inc := by
    simp
    intro e hemap x hx
    simp_all

    have : Option.isSome (G.inc e) = true := by
      by_contra heNone
      rw [Option.not_isSome_iff_eq_none] at heNone
      simp [heNone] at hemap
      done

    simp [Option.get_map _ _ _ this, hemap] at hx
    rcases hx with ⟨u , hu, habsurd⟩
    simp [ite_eq_iff, hdistinct] at habsurd
    rcases habsurd with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
    <;> simp_all
    · exact G.range_inc e this hu



end MultiGraphDissociatedNames
