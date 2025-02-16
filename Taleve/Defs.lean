import Mathlib

namespace Taleve

inductive Piece where | I | O | T | S | Z | J | L
deriving DecidableEq, Fintype

inductive Mino where
| gray : Mino
| colored (p : Piece) : Mino
deriving DecidableEq, Fintype

abbrev Cell := Option Mino

def Row (w : ℕ) := Vector Cell w

instance (w) : DecidableEq (Row w) := by
  unfold Row
  infer_instance

def Row.mk {w} (row : Vector Cell w) : Row w := row

def Board (w h : ℕ) := Vector (Row w) h

instance (w h) : DecidableEq (Board w h) := by
  unfold Board
  infer_instance

namespace Board

variable {w h w' h' : ℕ}

def mk (board : Vector (Row w) h) : Board w h := board

def toVector (board : Board w h) : Vector (Vector Cell w) h := board

def get (board : Board w h) (x : Fin w) (y : Fin h) : Cell :=
  board.toVector[y][x]

def getD (board : Board w h) (x y : ℤ) (default : Cell) : Cell :=
  if _ : 0 ≤ x ∧ x < w ∧ 0 ≤ y ∧ y < h then
    board.toVector[y.toNat][x.toNat]
  else
    default

def getOrEmpty (board : Board w h) (x y : ℤ) : Cell := board.getD x y none

def getOrFull (board : Board w h) (x y : ℤ) : Cell := board.getD x y (some .gray)

def ofFn (fn : Fin w → Fin h → Cell) : Board w h :=
  .mk <| .ofFn fun y ↦ .mk <| .ofFn fun x ↦ fn x y

def paste (target : Board w h) (source : Board w' h') (ox oy : ℤ) : Board w h :=
  .ofFn fun x y ↦ source.getOrEmpty (x - ox) (y - oy) <|> target.get x y

def IsDisjointAt (target : Board w h) (source : Board w' h') (ox oy : ℤ) : Prop :=
  ∀ (x : Fin w') (y : Fin h'), source.get x y = none ∨ target.getOrFull (ox + x) (oy + y) = none

instance (target : Board w h) (source : Board w' h') (ox oy : ℤ) :
    Decidable (IsDisjointAt target source ox oy) := by
  unfold IsDisjointAt
  infer_instance

end Board

end Taleve
