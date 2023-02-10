Require Import Poly.
Require Import List.
Require Import String.

(* Tipo das fórmulas nor *)

Inductive LF :=
| Atom : string -> LF
| Nor : LF -> LF -> LF.

Notation "[ A ]" := (Atom A) (at level 50).
Notation "A ↓ B"   := (Nor A B) (at level 100).
Notation "~ A"     := (Nor A A).
Notation "A /\ B"  := (Nor (Nor A A) (Nor B B)).
Notation "A \/ B"  := (Nor (Nor A B) (Nor A B)).
Notation "A -> B"  := (Nor (Nor (Nor A A) B) (Nor (Nor A A) B)).

Inductive node :=
| Empty
| Node (SL : SignedLF LF).

Definition NORTableau
  (snapshot : poly_binary_tree node)
  (lc : list (check node))
  (listNodes : list node)
  (m : list(mem nat))
  (p : parameters) : stt node nat :=
  match listNodes with
  | nil => state _ _ (Leaf _ nil) nil nil
  | h::tl =>
      match h with
      | Empty => state _ _ (Leaf _ nil) nil nil
      | Node SF => 
          match SF with 
          | T _ b L =>
              match L with
              | Atom _ => state _ _ (Leaf _ (explode listNodes)) nil nil
              | Nor P Q =>
                  if b then
                    let node1 := (Node (T _ false P)) in
                    let node2 := (Node (T _ false Q)) in
                    state _ _ (Alpha _ node1 ((Alpha _ node2 (Leaf _ (node1::node2::(explode listNodes)))))) nil nil
                  else
                    let node1 := (Node (T _ true P)) in
                    let node2 := (Node (T _ true Q)) in
                    state _ _ (Beta _ (Alpha _ node1 ((Leaf _ (node1::(explode listNodes)))))
                      (Alpha _ node2 ((Leaf _ (node2::(explode listNodes)))))) nil nil
              end
          end
      end
  end.

Open Scope string_scope.

Definition P := "P".
Definition Q := "Q".
Definition R := "R".
Definition S := "S".
Definition X := "X".

Definition node1 := Node (T _ false (([R] /\ [P]) /\ ([X]))).
Definition node2 := Node (T _ false ([X])).
Definition listNodes := node1::nil.

Compute make _ _ NORTableau (makeInitialTree _ listNodes listNodes).
