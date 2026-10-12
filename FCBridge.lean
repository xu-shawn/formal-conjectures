import Queens
import Mathlib.Tactic

/-!
# Bridge: Ho's `Queens.main` to the Formal Conjectures declarations

The definitions and API below are copied unchanged from
`FormalConjectures/Arxiv/1907.09120/GreedyQueens.lean` (only the `@[category ...]`
attributes, which are Formal Conjectures specific, are dropped). The two target
statements are copied verbatim and proved from `Queens.main`.
-/

namespace FCBridge

open scoped goldenRatio

/--
`IsSafe f c r` says that a queen in row `r` of column `c` shares no row and no diagonal with the
queen in row `f c'` of column `c'`, for each `c' < c`.
-/
def IsSafe (f : ℕ → ℕ) (c r : ℕ) : Prop :=
  ∀ c' < c, f c' ≠ r ∧ f c' + c ≠ r + c' ∧ f c' + c' ≠ r + c

instance (f : ℕ → ℕ) (c : ℕ) : DecidablePred (IsSafe f c) :=
  fun _ ↦ inferInstanceAs (Decidable (∀ _ < _, _))

theorem exists_isSafe (f : ℕ → ℕ) (c : ℕ) : ∃ r, IsSafe f c r := by
  refine ⟨∑ i ∈ Finset.range c, f i + c + 1, fun c' hc' ↦ ?_⟩
  have := Finset.single_le_sum (fun i _ ↦ Nat.zero_le (f i)) (Finset.mem_range.2 hc')
  omega

/--
`queenRows n` lists the rows of the queens in columns `0, …, n - 1`. Each queen goes in the lowest
row that no queen in an earlier column attacks.
-/
def queenRows : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let l := queenRows n
    l ++ [Nat.find (exists_isSafe (l.getD · 0) n)]

/--
`greedyQueens c` is the row $S_c$ of the queen in column $c$.

This is the column-by-column version of the problem, due to Knuth. Dekking, Shallit and Sloane
note that it gives the same queens as the scan along antidiagonals.
-/
def greedyQueens (c : ℕ) : ℕ :=
  (queenRows (c + 1)).getD c 0

theorem length_queenRows (n : ℕ) : (queenRows n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [queenRows, ih]

theorem getD_queenRows {c n : ℕ} (h : c < n) : (queenRows n).getD c 0 = greedyQueens c := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · simp only [queenRows]
      rw [List.getD_append _ _ _ _ (by simpa [length_queenRows] using h), ih h]
    · rfl

/-- `greedyQueens c` is the lowest row that no queen in an earlier column attacks. -/
theorem greedyQueens_eq_find (c : ℕ) :
    greedyQueens c = Nat.find (exists_isSafe greedyQueens c) := by
  have key : ∀ r, IsSafe ((queenRows c).getD · 0) c r ↔ IsSafe greedyQueens c r :=
    fun r ↦ forall₂_congr fun c' hc' ↦ by simp only [getD_queenRows hc']
  rw [greedyQueens, queenRows]
  simp only [List.getD_append_right _ _ _ _ (length_queenRows c).le, length_queenRows,
    Nat.sub_self, List.getD_cons_zero]
  exact Nat.find_congr' (key _)

/-- The Formal Conjectures sequence is Ho's `Queens.q`. -/
theorem greedyQueens_eq_q (n : ℕ) : greedyQueens n = Queens.q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [greedyQueens_eq_find, Queens.q]
    refine Nat.find_congr' (fun {r} ↦ ⟨fun h i ↦ ?_, fun h c' hc' ↦ ?_⟩)
    · have heq := ih i.val i.isLt
      obtain ⟨h1, h2, h3⟩ := h i.val i.isLt
      show r ≠ Queens.q i.val ∧ r + i.val ≠ Queens.q i.val + n ∧
        r + n ≠ Queens.q i.val + i.val
      omega
    · have heq := ih c' hc'
      obtain ⟨h1, h2, h3⟩ : r ≠ Queens.q c' ∧ r + c' ≠ Queens.q c' + n ∧
        r + n ≠ Queens.q c' + c' := h ⟨c', hc'⟩
      omega

/-- `conjecture25.variants.explicit_bounds`, verbatim, from `Queens.main`. -/
theorem conjecture25.variants.explicit_bounds (c : ℕ) :
    (c < greedyQueens c → |(greedyQueens c : ℝ) - c * φ| < 5 / φ) ∧
    (greedyQueens c < c → |(greedyQueens c : ℝ) - c / φ| < 4 + 5 / φ) := by
  simpa [greedyQueens_eq_q] using Queens.main c

/-- `conjecture25`, verbatim, from `Queens.main`. -/
theorem conjecture25 :
    ∃ ε₁ ε₂ : ℝ, ∀ c : ℕ,
      (c < greedyQueens c → |(greedyQueens c : ℝ) - c * φ| < ε₁) ∧
      (greedyQueens c < c → |(greedyQueens c : ℝ) - c / φ| < ε₂) :=
  ⟨5 / φ, 4 + 5 / φ, conjecture25.variants.explicit_bounds⟩

#print axioms FCBridge.greedyQueens_eq_q
#print axioms FCBridge.conjecture25.variants.explicit_bounds
#print axioms FCBridge.conjecture25

end FCBridge
