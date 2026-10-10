import SquareKit.Combinators
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# General matrices as representations of linear maps

The scalar algebra is any commutative semiring, so this same representation
supports ordinary arithmetic and timing semirings. Finite index types give
the chosen coordinate representation. Unlike the arbitrary representations
in `Squares`, this representation has a proved inverse. Composition,
addition, scaling, and application are exported as actual squares.
-/
namespace MatrixBackend

variable (R : Type) [CommSemiring R]
variable (m n p : Type) [Fintype m] [Fintype n] [Fintype p]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

@[reducible] def representation : Squares.Rep where
  R := Matrix m n R
  S := (n → R) →ₗ[R] (m → R)
  decode := Matrix.toLin'

def encode (f : (n → R) →ₗ[R] (m → R)) : Matrix m n R := LinearMap.toMatrix' f

omit [Fintype m] [DecidableEq m] in
theorem decode_encode (f : (n → R) →ₗ[R] (m → R)) :
    (representation R m n).decode (encode R m n f) = f := Matrix.toLin'_toMatrix' f

omit [Fintype m] [DecidableEq m] in
theorem encode_decode (M : Matrix m n R) :
    encode R m n ((representation R m n).decode M) = M := LinearMap.toMatrix'_toLin' M

def compositionSquare : Squares.Square
    (Squares.product (representation R p m) (representation R m n))
    (representation R p n) where
  impl q := q.1 * q.2
  spec q := q.1.comp q.2
  commutes q := Matrix.toLin'_mul q.1 q.2

def identitySquare : Squares.Square Squares.terminal (representation R n n) where
  impl _ := 1
  spec _ := LinearMap.id
  commutes _ := Matrix.toLin'_one

def additionSquare : Squares.Square
    (Squares.product (representation R m n) (representation R m n))
    (representation R m n) where
  impl q := q.1 + q.2
  spec q := q.1 + q.2
  commutes q := map_add Matrix.toLin' q.1 q.2

def scaleSquare (r : R) : Squares.Square (representation R m n) (representation R m n) where
  impl M := r • M
  spec f := r • f
  commutes M := map_smul Matrix.toLin' r M

def applicationSquare : Squares.Square
    (Squares.product (representation R m n) (Squares.exact (n → R)))
    (Squares.exact (m → R)) where
  impl q := q.1.mulVec q.2
  spec q := q.1 q.2
  commutes _ := rfl

/-- A linear map's coordinate transpose is its algebraic dual action. -/
def dual (f : (n → R) →ₗ[R] (m → R)) : (m → R) →ₗ[R] (n → R) :=
  Matrix.toLin' (LinearMap.toMatrix' f).transpose

def transposeSquare : Squares.Square (representation R m n) (representation R n m) where
  impl := Matrix.transpose
  spec := dual R m n
  commutes M := by simp [dual, representation]

omit [DecidableEq m] [DecidableEq n] in
theorem transpose_pairing (M : Matrix m n R) (v : n → R) (w : m → R) :
    dotProduct w (M.mulVec v) = dotProduct (M.transpose.mulVec w) v := by
  rw [Matrix.mulVec_transpose]
  exact Matrix.dotProduct_mulVec w M v

omit [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem transpose_reverses_composition (M : Matrix p m R) (N : Matrix m n R) :
    (M * N).transpose = N.transpose * M.transpose := Matrix.transpose_mul M N

theorem dual_reverses_composition (f : (m → R) →ₗ[R] (p → R))
    (g : (n → R) →ₗ[R] (m → R)) :
    dual R p n (f.comp g) = (dual R m n g).comp (dual R p m f) := by
  simp only [dual, LinearMap.toMatrix'_comp, Matrix.transpose_mul, Matrix.toLin'_mul]

end MatrixBackend
