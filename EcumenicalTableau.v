Require Import Poly.
Require Import List.
Require Import String.

(* Tipo das fórmulas ecumênicas *)

Inductive LF := 
| Atom   : string -> LF
| Neg  : LF -> LF
| And  : LF -> LF -> LF
| iOr  : LF -> LF -> LF
| cOr  : LF -> LF -> LF
| iImp : LF -> LF -> LF
| cImp : LF -> LF -> LF.

Inductive node :=
| Node (SL : SignedLF LF) (n : nat)
| R : nat -> nat -> node.

Notation "[ A ]"   := (Atom A) (at level 50).
Notation "~ A"     := (Neg A).
Notation "A /\ B"  := (And A B).
Notation "A \/i B" := (iOr A B) (at level 100).
Notation "A \/c B" := (cOr A B) (at level 100).
Notation "A ->i B" := (iImp A B) (at level 90).
Notation "A ->c B" := (cImp A B) (at level 90).

(** Nesse tableau, a memória guarda o index mais alto da árvore **)

Definition EcumenicalTableau
  (snapshot : poly_binary_tree node)
  (lc : list (check node))
  (listNodes : list node)
  (m : list(mem nat))
  (p : parameters)
  : stt node nat :=
  let memvalue := getRecordValueFromMemory nat (pop m (empty _)) 0 in
  match listNodes with
  | nil => state _ _ (Leaf _ nil) lc m
  | h::tl =>
      match h with
      | R k j => state _ _ (Leaf _ listNodes) lc m
      | Node SF n =>
          match SF with
          | T _ t L =>
              let unaryRule :=
                (fun node =>
                   state _ _ (Alpha _ node (Leaf _ (node::(explode listNodes)))) lc m) in
              let negationFRule :=
                (fun node =>
                   let nrecord := record _ 0 (memvalue+1) in
                   state _ _
                     (Alpha _ (R memvalue (memvalue+1))
                        (Alpha _ node
                           (Leaf _ (node::(explode listNodes))))) lc (nrecord::nil)) in
              let alphaRule :=
                (fun node1 node2 =>
                   state _ _
                     (Alpha _ node1
                        ((Alpha _ node2
                            (Leaf _ (node1::node2::(explode listNodes)))))) lc m) in
              let betaRule :=
                (fun node1 node2 =>
                   state _ _
                     (Beta _
                        (Alpha _ node1
                           ((Leaf _ (node1::(explode listNodes)))))
                        (Alpha _ node2
                           ((Leaf _ (node2::(explode listNodes)))))) lc m) in
              let specialBeta :=
                (fun node =>
                   if getSelector p then
                   state _ _
                     (Alpha _ node (Leaf _ (node::(explode listNodes))))
                     ((checkpoint _ snapshot (selector false))::lc)
                     m
                   else
                     state _ _
                       (Alpha _ node (Leaf _ (node::(explode listNodes))))
                       lc
                       m
                ) in
              match L with
              | Atom _ => state _ _ (Leaf _ (explode listNodes)) lc m
              | l /\ r => 
                  let an1 := (Node (T _ true l) 0) in
                  let an2 := (Node (T _ true r) 0) in 
                  let bn1 := (Node (T _ false l) 0) in
                  let bn2 := (Node (T _ false r) 0) in
                  if t then alphaRule an1 an2
                  else betaRule bn1 bn2
              | l \/c r => 
                  let an1 := (Node (T _ true (Neg l)) 0) in
                  let an2 := (Node (T _ true (Neg r)) 0) in 
                  let bn1 := (Node (T _ false (Neg l)) 0) in
                  let bn2 := (Node (T _ false (Neg r)) 0) in
                  if t then betaRule bn1 bn2
                  else alphaRule an1 an2
              | l ->c r => 
                  let an1 := (Node (T _ true l) 0) in
                  let an2 := (Node (T _ true (Neg r)) 0) in 
                  let bn1 := (Node (T _ false l) 0) in
                  let bn2 := (Node (T _ false (Neg r)) 0) in
                  if t then betaRule bn1 bn2
                  else alphaRule an1 an2
              | l \/i r => 
                  let an1 := (Node (T _ false l) 0) in
                  let an2 := (Node (T _ false r) 0) in 
                  let bn1 := (Node (T _ true l) 0) in
                  let bn2 := (Node (T _ true r) 0) in
                  if t then betaRule bn1 bn2
                  else
                    match p with
                    | none => specialBeta an1
                    | selector b => if b then specialBeta an1
                                    else specialBeta an2
                    end
              | l ->i r => 
                  let an1 := (Node (T _ true l) 0) in
                  let an2 := (Node (T _ false r) 0) in 
                  let bn1 := (Node (T _ false l) 0) in
                  let bn2 := (Node (T _ true r) 0) in
                  if t then betaRule bn1 bn2
                  else alphaRule an1 an2
              | ~ r => 
                  let an1 := (Node (T _ false r) 0) in
                  let an2 := (Node (T _ true r) (memvalue+1)) in 
                  if t then unaryRule an1
                  else negationFRule an2
              end
          end
      end
  end.


Open Scope string_scope.

Definition P := "P".
Definition Q := "Q".
Definition S := "S".
Definition X := "X".

Definition node0 := Node (T _ false ((([S] \/i [P]) \/i ([X] \/i [S])))) 0.
Definition node1 := Node (T _ false (~([S]))) 0.
Definition node2 := Node (T _ false (([X] \/i [S]))) 0.
Definition listnodes := node0::nil.

Compute make _ _ EcumenicalTableau (makeInitialTree _ listnodes listnodes).

