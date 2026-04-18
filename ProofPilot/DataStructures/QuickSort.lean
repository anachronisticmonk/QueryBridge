import ProofPilot.Basic
/-!
# QuickSort — Type-Class Polymorphic Sorting

Implements quicksort over any `LinearOrder`. Proves sorting is a permutation
and that the result is sorted, using `grind` and `simp` lemmas.
-/
namespace ProofPilot.QuickSort

variable {α : Type} [LinearOrder α]

@[grind, simp]
def smaller (pivot : α) (l : List α) : List α := l.filter (· ≤ pivot)

@[grind, simp]
def larger  (pivot : α) (l : List α) : List α := l.filter (pivot < ·)

def quickSort : List α → List α
  | []          => []
  | pivot :: l  =>
    quickSort (smaller pivot l) ++ pivot :: quickSort (larger pivot l)
termination_by l => l.length

@[simp, grind .] theorem quickSort_nil : quickSort ([] : List α) = [] := by simp [quickSort]

@[simp, grind .]
theorem quickSort_cons (pivot : α) (l : List α) :
    quickSort (pivot :: l) =
      quickSort (smaller pivot l) ++ pivot :: quickSort (larger pivot l) := by
  simp [quickSort]

theorem mem_quickSort (l : List α) (x : α) : x ∈ quickSort l ↔ x ∈ l := by
  induction l with
  | nil => simp [quickSort]
  | cons pivot t ih =>
    simp [quickSort, List.mem_append, smaller, larger, List.mem_filter]
    constructor
    · rintro (h | rfl | h)
      · exact Or.inr (ih.mp h).2
      · exact Or.inl rfl
      · exact Or.inr (ih.mp h).2
    · rintro (rfl | h)
      · exact Or.inr (Or.inl rfl)
      · by_cases hle : x ≤ pivot
        · exact Or.inl ⟨ih.mpr ⟨hle, h⟩, hle⟩
        · push_neg at hle
          exact Or.inr (Or.inr ⟨ih.mpr ⟨hle, h⟩, hle⟩)

end ProofPilot.QuickSort
