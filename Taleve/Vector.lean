import Mathlib

namespace Vector

variable {α : Type*} {n m n' m' : ℕ}

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

def pasteGrid (target : Vector (Vector α n) m) (source : Vector (Vector α n') m')
    (offsetX offsetY : ℕ) : Vector (Vector α n) m :=
  .ofFn
    fun ⟨j, hj⟩ ↦
      if h : offsetY ≤ j ∧ j < offsetY + m' then
        target[j].paste source[j - offsetY].toArray offsetX
      else
        target[j]

@[simp]
theorem get_get_pasteGrid (target : Vector (Vector α n) m) (source : Vector (Vector α n') m')
    (offsetX offsetY i j : ℕ) (hi : i < n) (hj : j < m)
    (hoffsetXi : offsetX ≤ i) (hioffsetX : i < offsetX + n')
    (hoffsetYj : offsetY ≤ j) (hjoffsetY : j < offsetY + m') :
    (target.pasteGrid source offsetX offsetY)[j][i] = source[j - offsetY][i - offsetX] := by
  simp [pasteGrid, hoffsetXi, hioffsetX, hoffsetYj, hjoffsetY]

end Vector
