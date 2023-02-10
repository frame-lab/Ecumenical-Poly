Require Import String.
Require Import List.

Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.

(** Polymorphic trees **)


(**

[TODO-LIST]

*** Uma função de alta ordem para determinar o fechamento do tableau.


**)


Inductive mem (X : Type) :=
| empty
| record (i : nat) (v : X).

Definition getRecordValueFromMemory (X : Type) (m : mem X) (default : X) :=
  match m with
  | empty _ => default
  | record _ i v => v
  end.

Fixpoint getRecordValueFromIndex (X : Type) (lm : list (mem X)) (k : nat) (default : X) :=
  match lm with
  | nil => default
  | h::tl => match h with
             | empty _ => getRecordValueFromIndex _ tl k default
             | record _ i v => if (beq_nat k i) then v else getRecordValueFromIndex _ tl k default
             end
  end.

Definition getIndexFromMemory (X : Type) (m : mem X) :=
  match m with
  | empty _ => 0
  | record _ i v => i
  end.

Inductive poly_binary_tree (X: Type) :=
| Leaf : list X -> list X -> poly_binary_tree X
| Alpha : X -> poly_binary_tree X -> poly_binary_tree X
| Beta  : poly_binary_tree X -> poly_binary_tree X -> poly_binary_tree X.

Check Leaf _ (2::nil) nil.

Check Alpha _ 3 (Leaf _ (2::nil) nil).

Check Alpha _ 3 (Beta _ (Alpha _ 3 ((Alpha _ 4 (Leaf _ nil nil)))) (Alpha _ 2 (Leaf _ nil nil))).

(* Tipo das formulas lineares *)

Inductive lLF :=
| lAtom : string -> lLF
| Tensor : lLF -> lLF -> lLF.

Notation "l[ A ]l" := (lAtom A) (at level 50).
Notation "A ⊗ B"   := (Tensor A B) (at level 100).
(* Notation "! A"   := (Bang A B) (at level 100). *)

Inductive parameters :=
| none
| selector (b : bool).

Inductive SignedLF (X : Type) :=
| T (b : bool) (L : X).

<<<<<<< HEAD
Inductive node :=
| Empty
| Node (SL : SignedLF LF).

Inductive enode :=
| eEmpty
| eNode (SL : SignedLF eLF) (n : nat).

Inductive lnode :=
| lEmpty
| lNode (SL : SignedLF lLF).

Inductive modal_node :=
| MEmpty
| MNode (b : bool) (L : LF) (n : nat).

=======
>>>>>>> 4a9aed482e2af11fd66c2df0a397f66096369e2d
Inductive check (X : Type) :=
| checkpoint : poly_binary_tree X -> parameters -> check X.

Inductive stt (X Y : Type) := 
| state : poly_binary_tree X -> list (check X) -> list (mem Y) -> stt X Y.

(*****************)

Definition pop
  {X : Type}
  (l : list X) default :=
  match l with nil => default | h::tl => h end.

Definition explode
  {X : Type}
  (l : list X) := match l with nil => nil | h::tl => tl end.

Fixpoint upto (k : nat) :=
  match k with
  | 0 => nil
  | S n => S n :: upto n 
  end.

(** Implementação da operação power 
    power recebe uma lista de elementos tipo X (genérico) e retorna a lista de todas as sublistas

    Entrada: A B C D

    A 1
    B 2
    C 3
    D  4

    AB 2
    AC 3
    AD 4
    BC 3
    BD 4
    CD 4

    ABC 3
    ABD 4
    ACD 4
    BCD 4

      ABCD 4
  

    Para isso, criamos um novo tipo X : indexed X
 **)


Inductive indexed (X : Type) :=
| i (n : nat) (v : X).

Open Scope string_scope.

Check i _ 323 "A". (* indexed string *)
Check i _ 323 23. (* indexed nat *)

Close Scope string_scope.



Fixpoint getValueAtPosition {X : Type} (l : list X) (p : nat) (default: X) :=
  match l with
  | nil => default
  | h::tl => if (beq_nat p 0) then h else getValueAtPosition tl (p-1) default
  end.

Compute getValueAtPosition (1::2::3::4::5::nil) 3 0.

Fixpoint combine {X : Type} (k : nat) (v : list X) (l : list X) (startValue : nat) (default: X) :=
  match k with
  | O => nil
  | S n => (i _ (startValue+1) (v++(getValueAtPosition l startValue default)::nil))
             :: combine n v l (startValue + 1) default
  end.

Definition getIndex {X : Type} (el : indexed X) :=
  match el with
  | i _ k _ => k
  end.

Definition getValue {X : Type} (el : indexed X) :=
  match el with
  | i _ _ v => v
  end.

Fixpoint break {X : Type} (l : list X) (startIndex : nat):=
  match l with
  | nil => nil
  | h::tl => (i _ startIndex (h::nil))::(break tl (startIndex + 1))
  end.

Fixpoint combinator {X : Type} (li : list (indexed (list X))) (l : list X) (default : X) :=
  match li with
  | nil => nil
  | h::tl =>
      ((combine ((length l)-(getIndex h)) (getValue h) l (getIndex h) default))++(combinator tl l default)
  end.

Fixpoint select {X : Type} (li : list (indexed (list X))) (size : nat) :=
  match li with
  | nil => nil
  | h::tl => if ((getIndex h) <? size) then h :: (select tl size) else (select tl size)
  end.

Fixpoint power_r {X : Type} (li : list (indexed (list X))) (l : list X) (default : X) (i : nat) :=
  match i with
  | O => nil
  | S k =>
      let next := (combinator (select li (length l)) l default) in
      (next) ++ (power_r (select next (length l)) l default k)
  end.

Fixpoint getAllValuesFromIndexedList {X : Type} (l : list (indexed (list X))) : list (list X) :=
  match l with
  | nil => nil
  | h::tl => (getValue h)::(getAllValuesFromIndexedList tl)
  end.

Definition power {X : Type} (l : list X) (default : X) :=
  let b := break l 1 in
  getAllValuesFromIndexedList (b++(power_r b l default (length l))).

Compute break (1::2::3::4::nil) 1.

Open Scope string_scope.

Compute power ("A"::"B"::"C"::"D"::nil) "null".

Compute length (power ("A"::"B"::"C"::"D"::nil) "null") .
Compute length (power ("A"::"B"::"C"::"D"::"E"::nil) "null") .
Compute length (power ("A"::"B"::"C"::"D"::"E"::"F"::nil) "null") .
Compute length (power ("A"::"B"::"C"::"D"::"E"::"F"::"G"::nil) "null") .

Close Scope string_scope.

(***********************)

Definition getTreeFromState (X Y : Type) (s : stt X Y) :=
  match s with
  | state _ _ t _ _ => t
  end.

Definition getCheckpointListFromState (X Y : Type) (s : stt X Y) :=
  match s with
  | state _ _ _ l _ => l
  end.

Definition getMemoryFromState (X Y : Type) (s : stt X Y) :=
  match s with
  | state _ _ _ _ m => m
  end.

Fixpoint expand
  (X Y : Type)
  (apply : poly_binary_tree X -> list (check X) -> list X -> list X -> list (mem Y) -> parameters -> stt X Y)
  (t : poly_binary_tree X)
  (snapshot : poly_binary_tree X) (** Uma cópia da árvore completa em seu estado atual **)
  (params : parameters)
  (m : list (mem Y))
  (lc : list (check X))
  : stt X Y :=
  match t with
  | Leaf _ listNodes listR => apply snapshot lc listNodes listR m params
  | Alpha _ N nt =>
      let next := (expand X Y apply nt snapshot params m lc) in
      state X Y
        (Alpha X N (getTreeFromState X Y next))
        (getCheckpointListFromState X Y next)
        (getMemoryFromState X Y next)
  | Beta _ L R =>
      let nextl := (expand X Y apply L snapshot params m lc) in
      let nextr := (expand X Y apply R snapshot params m lc) in
      state X Y
        (Beta X (getTreeFromState X Y nextl) (getTreeFromState X Y nextr))
        ((getCheckpointListFromState X Y nextl)++(getCheckpointListFromState X Y nextr))
        ((getMemoryFromState X Y nextl)++(getMemoryFromState X Y nextr))
  end.

Definition getSelector (p : parameters) :=
  match p with
  | none => true
  | selector b => b
  end.

<<<<<<< HEAD
Definition type2Tableau
  (snapshot : poly_binary_tree enode)
  (lc : list (check enode))
  (listNodes : list enode)
  (p : parameters)
  : stt enode :=
  match listNodes with
  | nil => state _ (Leaf _ nil) lc
  | h::tl =>
      match h with
      | eEmpty => state _ (Leaf _ nil) lc
      | eNode SF n =>
          match SF with
          | T _ t L =>
              let unaryRule :=
                (fun node =>
                   state _ (Alpha _ node (Leaf _ (node::(explode listNodes)))) lc) in
              let alphaRule :=
                (fun node1 node2 =>
                   state _ (Alpha _ node1 ((Alpha _ node2 (Leaf _ (node1::node2::(explode listNodes)))))) lc) in
              let betaRule :=
                (fun node1 node2 =>
                   state _ (Beta _ (Alpha _ node1 ((Leaf _ (node1::(explode listNodes)))))
                              (Alpha _ node2 ((Leaf _ (node2::(explode listNodes)))))) lc) in
              let specialBeta :=
                (fun node =>
                   if getSelector p then
                   state _
                     (Alpha _ node (Leaf _ (node::(explode listNodes))))
                     ((checkpoint _ snapshot)::lc)
                   else
                     state _
                       (Alpha _ node (Leaf _ (node::(explode listNodes))))
                       (lc)
                ) in
              match L with
              | eAtom _ => state _ (Leaf _ (explode listNodes)) lc
              | l /\e r => 
                  let an1 := (eNode (T _ true l) 0) in
                  let an2 := (eNode (T _ true r) 0) in 
                  let bn1 := (eNode (T _ false l) 0) in
                  let bn2 := (eNode (T _ false r) 0) in
                  if t then alphaRule an1 an2
                  else betaRule bn1 bn2
              | l \/c r => 
                  let an1 := (eNode (T _ true (Neg l)) 0) in
                  let an2 := (eNode (T _ true (Neg r)) 0) in 
                  let bn1 := (eNode (T _ false (Neg l)) 0) in
                  let bn2 := (eNode (T _ false (Neg r)) 0) in
                  if t then betaRule bn1 bn2
                  else alphaRule an1 an2
              | l ->c r => 
                  let an1 := (eNode (T _ true l) 0) in
                  let an2 := (eNode (T _ true (Neg r)) 0) in 
                  let bn1 := (eNode (T _ false l) 0) in
                  let bn2 := (eNode (T _ false (Neg r)) 0) in
                  if t then betaRule bn1 bn2
                  else alphaRule an1 an2
              | l \/i r => 
                  let an1 := (eNode (T _ false l) 0) in
                  let an2 := (eNode (T _ false r) 0) in 
                  let bn1 := (eNode (T _ true l) 0) in
                  let bn2 := (eNode (T _ true r) 0) in
                  if t then betaRule bn1 bn2
                  else
                    match p with
                    | none => specialBeta an1
                    | selector b => if b then specialBeta an1
                                    else specialBeta an2
                    end
              | l ->i r => 
                  let an1 := (eNode (T _ true l) 0) in
                  let an2 := (eNode (T _ false r) 0) in 
                  let bn1 := (eNode (T _ false l) 0) in
                  let bn2 := (eNode (T _ true r) 0) in
                  if t then betaRule bn1 bn2
                  else alphaRule an1 an2
              | ~e r => 
                  let an1 := (eNode (T _ false r) 0) in
                  let an2 := (eNode (T _ true r) 0) in 
                  if t then unaryRule an1
                  else unaryRule an2
              end
          end
      end
  end.

(** Recebe uma lista de nós abertos e retorna uma lista de 
lista com todas as combinações **)

Fixpoint combinationHelper 
(n : nat) 
(listNodes : list nat) : list (list nat) :=
  match listNodes with
  | nil => nil
  | h::tl => (n::tl)::(combinationHelper n tl)
  end.

Fixpoint linearCombinations (listNodes : list nat) :=
  match listNodes with 
  | nil => nil
  | h::tl => 
    (combinationHelper h tl)++(linearCombinations tl)
  end.

Compute linearCombinations (3::4::5::nil).

Compute partition _ (2::3::4::5::nil).

Definition type3Tableau
  (snapshot : poly_binary_tree lnode)
  (lc : list (check lnode))
  (listNodes : list lnode)
  (p : parameters) : stt lnode :=
  match listNodes with
  | nil => state _ (Leaf _ nil) lc
  | h::tl =>
      match h with
      | lEmpty => state _ (Leaf _ nil) lc
      | lNode SF =>
          match SF with
          | T _ t L =>
            match L with
            | lAtom _ => state _ (Leaf _ (explode listNodes)) lc
            | Tensor A B => state _ (Leaf _ (explode listNodes)) lc
      end
    end
  end
end.

=======
>>>>>>> 4a9aed482e2af11fd66c2df0a397f66096369e2d
Fixpoint construct
  (X Y : Type)
  (apply : poly_binary_tree X -> list (check X) -> list X -> list X -> list (mem Y) -> parameters -> stt X Y)
  (deepness : list nat)
  (t : poly_binary_tree X)
  (l : list (check X))
  (m : list (mem Y))
  (p : parameters) : stt X Y:= 
  match deepness with 
  | nil => state _ _ t l m
  | h::tl =>
      let next := (expand X Y apply t t p m l) in
      construct X Y
        apply tl
        (getTreeFromState X Y next)
        (getCheckpointListFromState X Y next)
        (getMemoryFromState X Y next)
        p
  end.

Definition getTreeFromCheckpoint (X : Type) (c : check X) :=
  match c with
  | checkpoint _ t _ => t
  end.

Definition getParamsFromCheckpoint (X : Type) (c : check X) :=
  match c with
  | checkpoint _ _ p => p
  end.

Fixpoint makeNewCheckpointList (X Y: Type) (l : list (stt X Y)) :=
  match l with
  | nil => nil
  | a::tl => (getCheckpointListFromState X Y a) ++ (makeNewCheckpointList X Y tl)
  end.

Fixpoint getAllTreesFromListState (X Y : Type) (l : list (stt X Y)) :=
  match l with
  | nil => nil
  | a::tl => (getTreeFromState X Y a ) :: (getAllTreesFromListState X Y tl)
  end.
  
(** Output: lista de states **)
Fixpoint checkpoint_handler
  (X Y : Type)
  (apply : poly_binary_tree X -> list (check X) -> list X -> list X -> list (mem Y) -> parameters -> stt X Y)
  (deepness : list nat)
  (lc : list (check X))
  (m : list (mem Y))
  (p : parameters) :=
  match lc with
  | nil => nil
  | h::tl =>
      let tree := getTreeFromCheckpoint _ h in
      let params := getParamsFromCheckpoint _ h in
      let ntree := getTreeFromState X Y (expand X Y apply tree tree params m nil) in
      let nstate := construct X Y apply deepness ntree nil m p in
      (nstate)::(checkpoint_handler X Y apply deepness tl m p)
  end.

Fixpoint controller
  (X Y: Type)
  (apply : poly_binary_tree X -> list (check X) -> list X -> list X -> list (mem Y) -> parameters -> stt X Y)
  (deepness : list nat)
  (l : list (check X))
  (m : list (mem Y))
  (p : parameters) :=
  let control := checkpoint_handler X Y apply deepness l m p in
  let newcps := makeNewCheckpointList X Y control in
  match deepness with
  | nil => nil
  | h::tl => (getAllTreesFromListState X Y control)++(controller X Y apply tl newcps m p)
  end.

Definition make
<<<<<<< HEAD
  (X : Type)
  (apply : poly_binary_tree X -> list (check X) -> list X -> parameters -> stt X)
=======
  (X Y : Type)
  (apply : poly_binary_tree X -> list (check X) -> list X -> list X -> list (mem Y) -> parameters -> stt X Y)
>>>>>>> 4a9aed482e2af11fd66c2df0a397f66096369e2d
  (initialTree : poly_binary_tree X)
  (steps : nat)
  :=
  let deepness := (upto steps) in
  let p := none in
  let start_ := construct X Y apply deepness initialTree nil ((empty Y)::nil) p in
  let checks := getCheckpointListFromState X Y start_ in
  let m := getMemoryFromState X Y start_ in
  (getTreeFromState X Y start_)::(controller X Y apply deepness checks m p).
