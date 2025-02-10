import Mathlib

namespace Vector

variable {α : Type*} {n : ℕ}

def paste (target : Vector α n) (source : Array α) (offset : ℕ) : Vector α n :=
  .ofFn
    fun ⟨i, hi⟩ ↦
      if h : offset ≤ i ∧ i < offset + source.size then
        source[i - offset]
      else
        target[i]

@[simp]
theorem get_paste (target : Vector α n) (source : Array α) (offset i : ℕ) (hi : i < n)
    (hoffseti : offset ≤ i) (hioffset : i < offset + source.size) :
    (target.paste source offset)[i] = source[i - offset] := by
  simp [paste, hoffseti, hioffset]

end Vector
