Require Import Coq.Lists.List.
Require Import Io.All.
Require Import System.All.
Require Import ListString.All.
Require Import String.
Require Import Json.
Import ListNotations.
Import C.Notations.
Import JsonNotations.
Local Open Scope json_scope.
Require Import Ascii.

Require Import String.



Definition header := "Require Import Coq.Lists.List.
Require Import Io.All.
Require Import System.All.
Require Import ListString.All.
Require Import String.
(* Local Open Scope string_scope. *)
Open Scope string_scope.


Require Import Json.

Import ListNotations.
Import C.Notations.
Import JsonNotations.
Local Open Scope json_scope.
Delimit Scope json_scope with json.
Require Import Ascii.

Definition js := "%string.



Fixpoint rev' {A} (a: list A) (acc: list A): list A :=
match a with 
| cons tail body => rev'(body)(cons tail acc)
| nil => acc  
end
.

Fixpoint concat'' {A} (b: list A) (a: list A) :=
match b with
| cons tail body => concat'' (body)(cons tail a)
| nil => a
end
.
Definition cons'{A} (b: list A)( a: list A) := concat'' (rev' b []) a.

(* Compute cons' [3 ; 4] [1 ; 2]. *)




Fixpoint split_json2 (s: LString.t) (context_stack: list ascii) (current_word: string) (acc: LString.t) : LString.t:=
match s with 
| head :: body => match head with 
                  | "\"%char => split_json2 (body) (head :: context_stack) (EmptyString) (head :: acc)
                  | "{"%char => match context_stack with 
                                (* | "" *)
                                | ":"%char :: tail => split_json2 (body) (head :: tail) (EmptyString) (head :: acc)
                                | _ => split_json2 (body) (head :: context_stack) (EmptyString) (head :: acc)
                                end
                  
                  | ":"%char => match context_stack with 
                                (* | """"%char :: tail => split_json2 (body) (context_stack) (EmptyString) (head :: acc) *)
                                | "{"%char :: tail => split_json2 (body) (head :: context_stack) (EmptyString) (" "%char ::"#"%char :: " "%char :: acc)
                                | _ => split_json2 (body) (context_stack) (EmptyString) ((*head*)":"%char :: acc)
                                end
                  | "}"%char => match context_stack with 
                                | "{"%char :: tail => split_json2 (body) (tail) (EmptyString) (head :: acc)
                                | "^"%char :: "{"%char :: tail => split_json2 (body) (tail) (EmptyString)(head :: """"%char :: acc)
                                | _ => split_json2 (body) (context_stack) (EmptyString) (head :: acc)
                                end
                  | ","%char => match context_stack with 
                                | "{"%char :: tail => split_json2 (body) (context_stack) (EmptyString) (","%char :: acc)
                                | "["%char :: tail => split_json2 (body) (context_stack) (EmptyString) (";"%char :: acc)
                                | "^"%char :: "{"%char :: tail => split_json2(body) ("{"%char :: tail) (EmptyString) (","%char ::""""%char :: acc)
                                | "^"%char :: "["%char :: tail => split_json2(body) ("["%char :: tail) (EmptyString) (";"%char ::""""%char :: acc)
                                | _ => split_json2 (body) (context_stack) (EmptyString) (head :: acc)
                                end
                  | "]"%char =>  match context_stack with 
                                | "["%char :: tail => split_json2 (body) (tail) (EmptyString) (head :: acc)
                                | "^"%char :: "["%char :: tail => split_json2 (body) (tail) (EmptyString)(head :: """"%char :: acc)
                                | _ => split_json2 (body) (context_stack) (EmptyString) (head :: acc)
                                end
                  | " "%char => match context_stack with 
                                | _ => split_json2 (body) (context_stack) (EmptyString) (head :: acc)     
                                end 
                  | "010"%char(*\n*) => split_json2 (body) (context_stack) (EmptyString) (head :: acc)     
                  | "["%char => match context_stack with 
                                | ":"%char :: tail => split_json2 (body) ("["%char :: tail) (EmptyString) ("["%char :: "'"%char :: acc)
                                | _ => split_json2 (body) ("["%char :: context_stack) (EmptyString) ("["%char :: "'"%char :: acc)
                                end
                  | """"%char =>  match context_stack with 
                                   | "\"%char :: tail  => split_json2(body)(tail)(EmptyString)(acc)
                                  | ":"%char :: tail => split_json2(body) (head :: tail)(EmptyString) (head ::"$"%char :: acc)
                                  | """"%char :: tail => split_json2 (body) (tail) (EmptyString) (head :: acc)
                                  | "["%char :: tail => split_json2(body)(head :: context_stack) (EmptyString)(head :: "$"%char :: acc)
                                  | _ => split_json2 (body) (context_stack) (EmptyString) (head :: acc)(*слабое место*)
                                  end
                  | _ =>  match context_stack with 
                              | "\"%char :: tail => split_json2 (body) (tail) (EmptyString) (head :: acc)
                              | "{"%char :: tail => split_json2 (body) (context_stack) (EmptyString) (head :: acc)
                              | "["%char :: tail =>  split_json2 (body) ("^"%char :: context_stack) (EmptyString) (head :: """"%char :: "$"%char :: acc) 
                              | ":"%char :: tail => split_json2 (body) ("^"%char :: tail) (EmptyString) (head :: """"%char :: "$"%char :: acc) 
                              |  _ => split_json2 (body) (context_stack) (EmptyString) (head :: acc)
                              end
                  end
| nil => acc
end
.



Definition translator2 (argv : list LString.t) : C.t System.effect Datatypes.unit :=
  let! a := match argv with
| [ _; file1 ] =>
    let! c := System.read_file file1 in
    match c with
    (* | Some c' => System.write_file (LString.s "foo") ( str2t ( header ++ (   all_oper   (t2str c') +++ "." ))  (* LString.s (header ++ (all_oper (t2str c')) ++ "."%string ) *)) *)
    | Some c' => System.write_file (LString.s "json_keeper.v") ((cons' (LString.s header) (rev'("."%char ::(split_json2 (c' ) [ ] ""%string []))[])))
    | _       => System.write_file (LString.s "json_keeper.v") (LString.s "Cannot read the files."%string)
    end
| _ => System.write_file (LString.s "foo.v") (LString.s "Expected a parameter."%string)
  end in System.log (LString.s "ok").

Definition main := Extraction.launch translator2.

(* Check Extraction.launch.
Check main. *)
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extraction "jsonToCoqFile" main.