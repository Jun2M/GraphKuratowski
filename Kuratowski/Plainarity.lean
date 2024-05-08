import Mathlib.Data.Real.Basic
import Kuratowski.MultiGraphOrd


namespace MultiGraph
variable (αᵥ αₑ : Type u)

structure PlainarEmbedding (G : MultiGraph αᵥ αₑ) :=
  (vertexEmbedding : αᵥ → ℝ × ℝ)
  (edgeEmbedding : αₑ → Set.Icc 0 1 → ℝ × ℝ)
  (embedding_intersections : ∀ e₁ e₂, e₁ ≠ e₂ →
    ¬ ∃ t₁ t₂, 0 < t₁.val ∧ t₁.val < 1 ∧ 0 < t₂.val ∧ t₂.val < 1 ∧
      edgeEmbedding e₁ t₁ = edgeEmbedding e₂ t₂)
  (embedding_ends : )



end MultiGraph
