import Std

/-!
# Q3 cubical curl map: finite algebraic rank and reconstruction facts

The cube graph Q3 has 8 vertices, 12 oriented edges (lower label to higher label) and 6 square faces.
The curl map sends an edge-phase vector to the six signed face sums. Each theorem is a closed finite
computation over the integers, checked by kernel evaluation; no physical claim is made.

* `bianchi_left_null`: the alternating face combination (-1,1,1,-1,-1,1) annihilates every edge column.
* `vertex_gauge_in_kernel`: the curl of each vertex-potential gradient is zero (7 independent gauge directions).
* `chord_minors_unimodular`: after fixing the spanning tree (0,1),(0,2),(0,4),(1,3),(1,5),(2,6),(3,7), omitting
  any one face leaves a 5x5 chord block of determinant +-1, so five faces determine the five cycle phases
  integrally (and hence modulo 2 pi).
* `four_face_subsets_have_rank_four`: every four-face subset has a nonzero 4x4 chord minor.

Edge order, face order and the face orientation reproduce `q3_curvature.py` in
`research/arithmetic_holonomy_rotor/ibm_qpu_01`; `research/pregeometric_identifiability/q3_minimal_observation.py`
checks the same facts with exact rational arithmetic and records the noisy-measurement studies.
-/

namespace MathCan.Pregeometry.Q3

def edges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)]

def faces : List (List Nat) :=
  [[0, 1, 3, 2], [4, 5, 7, 6], [0, 1, 5, 4], [2, 3, 7, 6], [0, 2, 6, 4], [1, 3, 7, 5]]

def bianchi : List Int := [-1, 1, 1, -1, -1, 1]

/-- Signed incidence of the cyclic face boundary with one oriented edge. -/
def curlEntry (face : List Nat) (e : Nat × Nat) : Int :=
  (face.zip (face.drop 1 ++ face.take 1)).foldl
    (fun acc p =>
      if p.1 < p.2 && (p.1, p.2) == e then acc + 1
      else if p.2 < p.1 && (p.2, p.1) == e then acc - 1
      else acc) 0

def curl : List (List Int) := faces.map (fun f => edges.map (curlEntry f))

/-- Gradient of the vertex potential `delta_v` evaluated on the edge `(a, b)`. -/
def gradEntry (e : Nat × Nat) (v : Nat) : Int :=
  if e.2 == v then 1 else if e.1 == v then -1 else 0

/-- Indices (in `edges`) of the non-tree edges (2,3),(4,5),(4,6),(5,7),(6,7). -/
def chordCols : List Nat := [5, 8, 9, 10, 11]

def chordRow (f : Nat) : List Int := chordCols.map (fun c => (curl.getD f []).getD c 0)

def detAux : Nat → List (List Int) → Int
  | 0, _ => 0
  | _ + 1, [] => 1
  | n + 1, r :: rs =>
    (List.range r.length).foldl
      (fun acc j =>
        let sign : Int := if j % 2 == 0 then 1 else -1
        acc + sign * r.getD j 0 * detAux n (rs.map (fun row => row.eraseIdx j))) 0

theorem curl_shape : curl.length = 6 ∧ curl.all (fun r => r.length == 12) = true := by
  decide +kernel

theorem bianchi_left_null :
    (List.range 12).all (fun e =>
      (List.range 6).foldl (fun acc f => acc + bianchi.getD f 0 * (curl.getD f []).getD e 0) 0 == 0) = true := by
  decide +kernel

theorem vertex_gauge_in_kernel :
    (List.range 6).all (fun f => (List.range 8).all (fun v =>
      (List.range 12).foldl
        (fun acc e => acc + (curl.getD f []).getD e 0 * gradEntry (edges.getD e (0, 0)) v) 0 == 0)) = true := by
  decide +kernel

/-- Omitting face `k` leaves a unimodular 5x5 chord block. -/
theorem chord_minors_unimodular :
    (List.range 6).map (fun k => detAux 6 (((List.range 6).map chordRow).eraseIdx k)) = [-1, -1, 1, 1, -1, -1] := by
  decide +kernel

def fourSubsets : List (List Nat) :=
  (List.range 6).flatMap (fun i => (List.range 6).filterMap (fun j =>
    if i < j then some ((List.range 6).filter (fun f => f != i && f != j)) else none))

theorem four_face_subsets_count : fourSubsets.length = 15 := by decide +kernel

theorem four_face_subsets_have_rank_four :
    fourSubsets.all (fun S => (List.range 5).any (fun c =>
      detAux 5 ((S.map chordRow).map (fun row => row.eraseIdx c)) != 0)) = true := by
  decide +kernel

#print axioms curl_shape
#print axioms bianchi_left_null
#print axioms vertex_gauge_in_kernel
#print axioms chord_minors_unimodular
#print axioms four_face_subsets_count
#print axioms four_face_subsets_have_rank_four

end MathCan.Pregeometry.Q3
