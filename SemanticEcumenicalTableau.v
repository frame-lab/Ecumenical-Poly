Require Import Poly.
Require Import List.
Require Import String.
Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.


(* Tipo das fórmulas ecumênicas *)

(** TODO : 

1) regras dos operadores
2) regras da hereditariedade

**)

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

Definition getMinFromNode (n : node) :=
  match n with
  | Node _ k => k
  | R k j => k
  end.

Definition getMaxFromNode (n : node) :=
  match n with
  | Node _ k => k
  | R k j => j
  end.

Notation "@ A"   := (Atom A) (at level 50).
Notation "~ A"     := (Neg A).
Notation "A /\ B"  := (And A B).
Notation "A \/i B" := (iOr A B) (at level 100).
Notation "A \/c B" := (cOr A B) (at level 100).
Notation "A ->i B" := (iImp A B) (at level 90).
Notation "A ->c B" := (cImp A B) (at level 90).

Definition eqb_node_R (A : node) (B : node) :=
  match A with
  | R k j =>
      match B with
      | R k1 j1 => if andb (beq_nat k k1) (beq_nat j j1) then true
                   else false
      | _ => false
      end
  | _ => false        
  end.

Fixpoint checkIfRIsInList (A : node) (l : list node) :=
  match l with
  | nil => false
  | h::tl =>  orb (eqb_node_R A h) (checkIfRIsInList A tl)
  end.

Require Import List.
Import ListNotations.

Definition l := [(R 2 1);(R 0 1);(R 1 1);(R 1 2);(R 1 3)].

Compute checkIfRIsInList (R 0 2) l.

(** Nesse tableau, a memória de um ramo S guarda todos os R x y do ramo S **)

Definition Reflexivity (n : nat) : node := R n n.

Fixpoint CloseRToTransitivity (n : node) (ln : list node) (cp_ln : list node) :=
  match ln with
  | nil => nil
  | h::tl => match h with
             | Node _ k => CloseRToTransitivity n tl cp_ln
             | R k j => if (beq_nat j (getMinFromNode n))
                        then if negb (checkIfRIsInList (R k (getMaxFromNode n)) cp_ln)
                             then (R k (getMaxFromNode n))
                                    ::(CloseRToTransitivity n tl cp_ln)
                             else (CloseRToTransitivity n tl cp_ln)
                        else (CloseRToTransitivity n tl cp_ln)
             end
  end.

Fixpoint RemoveAmbiguity (ln : list node) :=
  match ln with
  | nil => nil
  | h::tl => if checkIfRIsInList h tl then
               RemoveAmbiguity tl
             else h::(RemoveAmbiguity tl)
  end.

Definition Transitivity (n : node) (ln : list node) :=
  RemoveAmbiguity (CloseRToTransitivity n ln ln).

Compute CloseRToTransitivity (R 1 3) l l.

Fixpoint ListMemNodeToListNode (lm : list (mem node)) :=
  match lm with
  | nil => nil
  | h::tl => match h with
             | empty _ => (ListMemNodeToListNode tl)
             | record _ _ val => val::(ListMemNodeToListNode tl)
             end
  end.

Fixpoint ListNodeToMemNode (ln : list node) :=
  match ln with
  | nil => nil
  | h::tl => (record _ 0 h)::(ListNodeToMemNode tl)
  end.

Compute ListNodeToMemNode (CloseRToTransitivity (R 1 2) l l).

Compute checkIfRIsInList (R 0 0) [R 0 0; R 0 2; R 1 2; R 0 1].

Fixpoint makeInitialTree (l : list node) (listNodes : list node) :=
  match l with
  | nil => Alpha _ (R 0 0) (Leaf _ listNodes ((R 0 0)::nil))
  | h::tl => Alpha _ h (makeInitialTree tl listNodes)
  end.

Definition SemanticEcumenicalTableau
  (snapshot : poly_binary_tree node)
  (lc : list (check node))
  (listNodes : list node)
  (listR : list node)
  (m : list (mem node))
  (p : parameters)
  : stt node node :=
  let memvalue :=
    getMaxFromNode (pop listR (R 0 0)) in
  match listNodes with
  | nil => state _ _ (Leaf _ nil listR) lc m
  | h::tl =>
      match h with
      | R k j => if (checkIfRIsInList (R k j) listR) then
                   state _ _
                     (Leaf _ (explode listNodes) (listR))
                     lc m
                 else
                   state _ _
                     (Alpha _ (R k j) (Leaf _ (explode listNodes) ((R k j)::listR)))
                     lc m
      | Node SF n =>
          match SF with
          | T _ t L =>
              let unaryRule :=
                (fun node =>
                   state _ _ (Alpha _ node
                                (Leaf _ (node::(explode listNodes)) listR)) lc m) in
              let negationFRule :=
                (fun node =>
                   let nrecord := record _ 0 (R n (memvalue+1)) in
                   let transClosure := (Transitivity (R n (memvalue+1))
                                          listR) in
                   state _ _
                     (Alpha _ (R n (memvalue+1))
                        (Alpha _ (Reflexivity (memvalue+1))
                           (Alpha _ node
                              (Leaf _
                                 (transClosure++(node::(explode listNodes)))
                                 ((R n (memvalue+1))::(Reflexivity (memvalue+1))::listR)))))
                     lc
                     m) in
              let alphaRule :=
                (fun node1 node2 =>
                   state _ _
                     (Alpha _ node1
                        ((Alpha _ node2
                            (Leaf _ (node1::node2::(explode listNodes)) listR)))) lc m) in
              let betaRule :=
                (fun node1 node2 =>
                   state _ _
                     (Beta _
                        (Alpha _ node1
                           ((Leaf _ (node1::(explode listNodes)) listR)))
                        (Alpha _ node2
                           ((Leaf _ (node2::(explode listNodes)) listR)))) lc m) in
              match L with
              | Atom _ => state _ _ (Leaf _ (explode listNodes) listR) lc m
              | l /\ r => 
                  let an1 := (Node (T _ true l) n) in
                  let an2 := (Node (T _ true r) n) in 
                  let bn1 := (Node (T _ false l) n) in
                  let bn2 := (Node (T _ false r) n) in
                  if t then alphaRule an1 an2
                  else betaRule bn1 bn2
              | l \/c r => 
                  let an1 := (Node (T _ true (Neg l)) n) in
                  let an2 := (Node (T _ true (Neg r)) n) in 
                  let bn1 := (Node (T _ false (Neg l)) n) in
                  let bn2 := (Node (T _ false (Neg r)) n) in
                  if t then betaRule bn1 bn2
                  else alphaRule an1 an2
              | l ->c r => 
                  let an1 := (Node (T _ true l) n) in
                  let an2 := (Node (T _ true (Neg r)) n) in 
                  let bn1 := (Node (T _ false l) n) in
                  let bn2 := (Node (T _ false (Neg r)) n) in
                  if t then betaRule bn1 bn2
                  else alphaRule an1 an2
              | l \/i r => 
                  let an1 := (Node (T _ false l) n) in
                  let an2 := (Node (T _ false r) n) in 
                  let bn1 := (Node (T _ true l) n) in
                  let bn2 := (Node (T _ true r) n) in
                  if t then betaRule bn1 bn2
                  else alphaRule an1 an2
              | l ->i r => 
                  let an1 := (Node (T _ true l) n) in
                  let an2 := (Node (T _ false r) n) in 
                  let bn1 := (Node (T _ false l) n) in
                  let bn2 := (Node (T _ true r) n) in
                  if t then betaRule bn1 bn2
                  else alphaRule an1 an2
              | ~ r => 
                  let an1 := (Node (T _ false r) n) in
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

Definition node0 := Node (T _ true (@S \/i @P)) 0.
Definition node1 := Node (T _ false (~(@S /\ ~~(@P /\ @Q)))) 0.
Definition node2 := Node (T _ false (~((~~@X \/i ~~~~~@P) \/i ~~~~@S))) 0.
Definition node3 := Node (T _ false (@P \/i ~@P)) 0.

Definition listnodes := node3::nil.

Definition l1 := [(R 0 0);(R 1 2);(R 0 1)].

Compute RemoveAmbiguity (CloseRToTransitivity (R 2 3) l1 l1).
Compute Transitivity (R 1 2) l1.
Compute make _ _ SemanticEcumenicalTableau (makeInitialTree listnodes listnodes) 15.

