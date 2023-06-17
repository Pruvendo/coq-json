Require Import Coq.Lists.List.
Require Import Io.All.
Require Import System.All.
Require Import ListString.All.
Require Import String.
(* Require Import UtilityFunctions. *)
(* Require Import StringHelpers. *)
Require Import Json.
Import ListNotations.
Import C.Notations.
Import JsonNotations.
Require Import Ascii.

Local Open Scope json_scope.
Delimit Scope json_scope with json.
Open Scope string_scope.


Fixpoint drop_last(s:string):=
match s with 
| String a EmptyString => EmptyString
| String a b => String a (drop_last b)
|EmptyString => EmptyString
end    
.

Fixpoint replace'(old: string)(new: string) (s:string) (acc: string):=
match s with 
| String head body => let lenO := length old in 
                      let lenA := length acc in
                      if old =? substring 0 lenO acc
                      then replace' (old)(new)(body)(String (head)(new ++ substring lenO (lenA) acc))
                      else (replace' (old) (new) (body) (String (head) acc))
| EmptyString => let lenO := length old in 
                  let lenA := length acc in
                  if old =? substring (0) lenO acc
                  then  new ++ substring (lenO)(lenA) acc 
                  else  acc
end  
.


Definition replace(old: string)(new: string) (s:string) := 
let out := string_rev (replace' (string_rev old) (string_rev new) s "") in
out.



Fixpoint replaceWith(oldAndNew: list(string*string))(s:string):string :=
match oldAndNew with 
| tail :: body => let newS:= replace (fst tail)(snd tail) s in replaceWith body newS
| nil => s
end
.

Fixpoint reduce{A B}(f: A -> B -> B)(l : list A)(default: B): B :=
match l with 
| nil => default
| tail :: body =>  f (tail)(reduce (f)(body)(default)) 
end
.

Fixpoint pars(json_string:string)(depth_level: nat)(depth_const: nat): json :=
let mapping (json_str: string)(depth: nat)(const: nat):= 
match depth with 
| S depth' => 
    let pairs := split_string json_str ("$"++(writeNat(const - depth + 2))++"$") in 
    let pairs := map (fun pair => match split_string pair ":" with | a :: b=> (replaceWith[("""","")] a , (String.concat ":" b)) | _ => ("error", "error") end ) pairs in
    json_map(reduce (fun pair m => mapkv (fst pair) (pars (snd pair) depth' const) m) pairs empty)
| O => { }
end
in 
let listing (json_str: string)(depth: nat)(const: nat) := 
match depth with 
| S depth' => json_list (map (fun str => pars str depth' const) (split_string json_str ("$"++(writeNat(const - depth + 2))++"$")))
| O => '[ ]
end
in
match json_string with 
| String "{"%char b => mapping (drop_last b) depth_level depth_const
| String "["%char b => listing (drop_last b) depth_level depth_const
| String """"%char b => json_data (replaceWith[("""","")] b)
| _ => { }
end
.

Fixpoint app'{A} (a: list A)(b: list A): list A :=
match a with 
| head :: tail => head :: (app' tail  b)
| nil => b
end
.

Fixpoint reconfigure (s: LString.t) (context_stack: list ascii)(acc: LString.t)(depth: nat)(maxDepth:nat) : LString.t * nat:=
match s with 
| head :: body => match head with 
                  | "\"%char => reconfigure (body) (head :: context_stack)  (head :: acc)(depth)(maxDepth)
                  | "{"%char => match context_stack with 
                                (* | "" *)
                                | ":"%char :: tail => reconfigure (body) (head :: tail)  (head :: acc)(depth + 1)(if Nat.leb maxDepth (depth + 1) then (depth + 1) else maxDepth)
                                | _ => reconfigure (body) (head :: context_stack)  (head :: acc)(depth + 1)(if Nat.leb maxDepth (depth + 1) then (depth + 1) else maxDepth)
                                end
                  | ":"%char => match context_stack with 
                                (* | """"%char :: tail => reconfigure (body) (context_stack)  (head :: acc) *)
                                | "{"%char :: tail => reconfigure (body) (head :: context_stack)  (":"%char :: acc)(depth)(maxDepth)
                                | _ => reconfigure (body) (context_stack)  ((*head*)":"%char :: acc)(depth)(maxDepth)
                                end
                  | "}"%char => match context_stack with 
                                | "{"%char :: tail => reconfigure (body) (tail)  (head :: acc)(depth - 1)(maxDepth)
                                | "^"%char :: "{"%char :: tail => reconfigure (body) (tail) (head :: """"%char :: acc)(depth - 1)(maxDepth)
                                | _ => reconfigure (body) (context_stack)  (head :: acc)(depth)(maxDepth)
                                end
                  | ","%char => match context_stack with 
                                | "{"%char :: tail => reconfigure (body) (context_stack) (app' (LString.s ("$" ++ string_rev(writeNat (depth + 1)) ++ "$")) acc ) (*","%char :: acc*)(depth)(maxDepth)
                                | "["%char :: tail => reconfigure (body) (context_stack) (app' (LString.s ("$" ++ string_rev(writeNat (depth + 1)) ++ "$")) acc ) (*";"%char :: acc*)(depth)(maxDepth)
                                | "^"%char :: "{"%char :: tail => reconfigure(body) ("{"%char :: tail) ((app' (LString.s ("$" ++ string_rev(writeNat (depth + 1)) ++ "$")) (""""%char :: acc) )) (*","%char ::""""%char :: acc*)(depth)(maxDepth)
                                | "^"%char :: "["%char :: tail => reconfigure(body) ("["%char :: tail) ((app' (LString.s ("$" ++ string_rev(writeNat (depth + 1)) ++ "$")) (""""%char :: acc) )) (*";"%char ::""""%char :: acc*)(depth)(maxDepth)
                                | _ => reconfigure (body) (context_stack)  (head :: acc)(depth)(maxDepth)
                                end
                  | "]"%char =>  match context_stack with 
                                | "["%char :: tail => reconfigure (body) (tail)  (head :: acc)(depth - 1)(maxDepth)
                                | "^"%char :: "["%char :: tail => reconfigure (body) (tail) (head :: """"%char :: acc)(depth - 1)(maxDepth)
                                | _ => reconfigure (body) (context_stack)  (head :: acc)(depth)(maxDepth)
                                end
                  | " "%char => match context_stack with 
                                | "\"%char :: tail => reconfigure (body) (tail)  (head :: acc) (depth)(maxDepth)
                                | "{"%char :: tail => reconfigure (body) (context_stack)  (acc) (depth)(maxDepth)
                                | "["%char :: tail =>  reconfigure (body) (context_stack)  (acc) (depth)(maxDepth)
                                | "^"%char :: tail =>  reconfigure (body) (tail)  (""""%char::acc) (depth)(maxDepth)
                                | ":"%char :: tail => reconfigure (body) (context_stack)  (acc) (depth)(maxDepth)
                                | """"%char :: tail => reconfigure (body) (context_stack)  (head :: acc) (depth)(maxDepth)
                                |  _ => reconfigure (body) (context_stack)  (head :: acc) (depth)(maxDepth)
                                end
                    |"	"%char =>    match context_stack with 
                                    | "\"%char :: tail => reconfigure (body) (tail)  (head :: acc) (depth)(maxDepth)
                                    | "{"%char :: tail => reconfigure (body) (context_stack)  (acc) (depth)(maxDepth)
                                    | "["%char :: tail =>  reconfigure (body) (context_stack)  (acc) (depth)(maxDepth)
                                    | "^"%char :: tail =>  reconfigure (body) (tail)  (""""%char::acc) (depth)(maxDepth)
                                    | ":"%char :: tail => reconfigure (body) (context_stack)  (acc) (depth)(maxDepth)
                                    | """"%char :: tail => reconfigure (body) (context_stack)  (head :: acc) (depth)(maxDepth)
                                    |  _ => reconfigure (body) (context_stack)  (head :: acc) (depth)(maxDepth)
                                    end                     
                  | "010"%char(*\n*) => reconfigure (body) (context_stack)  ((*head ::*) acc) (depth)    (maxDepth)
                  | "["%char => match context_stack with 
                                | ":"%char :: tail => reconfigure (body) ("["%char :: tail)  ("["%char :: acc) (depth + 1)(if Nat.leb maxDepth (depth + 1) then (depth + 1) else maxDepth)
                                | _ => reconfigure (body) ("["%char :: context_stack)  ("["%char :: acc) (depth + 1)(if Nat.leb maxDepth (depth + 1) then (depth + 1) else maxDepth)
                                end
                  | """"%char =>  match context_stack with 
                                   | "\"%char :: tail  => reconfigure(body)(tail)(acc) (depth)(maxDepth)
                                  | ":"%char :: tail => reconfigure(body) (head :: tail) (head :: acc) (depth)(maxDepth)
                                  | """"%char :: tail => reconfigure (body) (tail)  (head :: acc) (depth)(maxDepth)
                                  | "["%char :: tail => reconfigure(body)(head :: context_stack) (head :: acc) (depth)(maxDepth)
                                  | _ => reconfigure (body) (context_stack)  (head :: acc)(*слабое место*) (depth)(maxDepth)
                                  end
                  | _ =>  match context_stack with 
                              | "\"%char :: tail => reconfigure (body) (tail)  (head :: acc) (depth)(maxDepth)
                              | "{"%char :: tail => reconfigure (body) (context_stack)  (head :: acc) (depth)(maxDepth)
                              | "["%char :: tail =>  reconfigure (body) ("^"%char :: context_stack)  (head :: """"%char :: acc) (depth)(maxDepth)
                              | ":"%char :: tail => reconfigure (body) ("^"%char :: tail)  (head :: """"%char :: acc) (depth)(maxDepth)
                              |  _ => reconfigure (body) (context_stack)  (head :: acc) (depth)(maxDepth)
                              end
                  end
| nil => (acc, maxDepth)
end
.

Fixpoint rev' {A} (a: list A) (acc: list A): list A :=
match a with 
| cons tail body => rev'(body)(cons tail acc)
| nil => acc  
end
.


Definition drop_last_space (str:string): string :=
let fix drop_last_space'(reversed_string: string):=
match reversed_string with 
| String " "%char b => drop_last_space' b 
| String "101"%char b => drop_last_space' b 
| String _ b =>  b 
| EmptyString =>  EmptyString 
end in 
string_rev (drop_last_space'(string_rev str))
.

Fixpoint t2str (t : LString.t): string :=
match t with 
| tail :: body => (String tail "")++t2str(body)
| nil => ""
end    
.

Definition str2Json_term(json_str:string) := 
let '(json_LStringt, depth ) := (reconfigure (LString.s json_str )[][] 0 0) in  
let json_string := (t2str (rev'(json_LStringt)[])) in 
let json_term := pars json_string depth depth in json_term.
Definition LStringt2Json_term(json_str:LString.t):json := let '(json_LStringt, depth ) := (reconfigure (json_str )[][] 0 0) in  
let json_string := (t2str (rev'(json_LStringt)[])) in 
let json_term := pars json_string depth depth in json_term.

Definition t2strPlusRev (t: LString.t):=
let fix t2strPlusRev' (t : LString.t)(acc: string) : string :=
  match t with
  | tail :: body => t2strPlusRev' body (String tail acc)
  | [] => acc
  end
  in t2strPlusRev' t EmptyString.
Fixpoint t2strPlusRev' (t : LString.t)(acc: string) : string :=
match t with
| tail :: body => t2strPlusRev' body ( String tail acc)
| [] => acc
end.
Fixpoint pars'(json_string:string)(depth_level: nat)(depth_const: nat): json :=
let mapping (json_str: string)(depth: nat)(const: nat):= 
match depth with 
| S depth' => 
    let pairs := split_string json_str ("$"++(writeNat(const - depth + 2))++"$") in 
    let fix split_by_2points(acc:string)(str:string):= 
    match str with 
    | String a b => 
        if Ascii.eqb a ":"
        then (string_rev acc, b)
        else split_by_2points (String a acc) b 
    | EmptyString => (string_rev acc, EmptyString)
    end
    in
    let pairs := map (split_by_2points EmptyString) pairs in
    let fix iter_map (pairs: list (string*string))(acc: key_map):key_map:= 
    match pairs with 
    | head :: tail => 
        let '(key, value):= head in 
        let key := replaceWith[("""","")] key in
        iter_map tail (mapkv key (pars' value depth' const) acc)
    | nil => acc
    end
    in
    json_map(iter_map (rev' pairs []) empty)
| O => { }
end
in 
let listing (json_str: string)(depth: nat)(const: nat) := 
match depth with 
| S depth' => json_list (map (fun str => pars' str depth' const) (split_string json_str ("$"++(writeNat(const - depth + 2))++"$")))
| O => '[ ]
end
in
match json_string with 
| String "{"%char b => mapping (drop_last b) depth_level depth_const
| String "["%char b => listing (drop_last b) depth_level depth_const
| String """"%char b => json_data (replaceWith[("""","")] b)
| _ => { }
end
.
Fixpoint is_prefix(prefix: LString.t)(word: LString.t):bool  :=
match prefix with 
| head_prefix :: tail_prefix =>   
    match word with 
    | head_word :: tail_word => 
        if Ascii.eqb head_prefix head_word 
        then is_prefix tail_prefix tail_word
        else false 
    | nil => false
    end
| nil => true
end
.

Fixpoint list_ascii_eqb(l1: LString.t)(l2: LString.t):bool:=
match l1 with 
| head1 :: tail1 =>
    match l2 with 
    | head2 :: tail2 => 
        if Ascii.eqb head1 head2 
        then list_ascii_eqb tail1 tail2 
        else false
    | nil  => false
    end
| nil => 
    match l2 with 
    | nil => true 
    | _ => false
    end
end    
.




Definition take_prefix(str: LString.t)(len: nat):=
let fix take_prefix'(str: LString.t)(len: nat)(acc:LString.t):=
match str with 
| head :: tail => 
    match len with 
    | 0 => acc 
    | _ => take_prefix' tail (len - 1) (head :: acc)
    end
| nil => acc
end in 
(take_prefix' str len nil)
.
Definition split_LString(str: LString.t)(sep:LString.t): list (LString.t):=
(* let sep := rev sep in  *)
let fix split_LString'
                    (str: LString.t)
                    (sep: LString.t)
                    (current_sep:LString.t)
                    (current_word: LString.t)
                    (acc: list LString.t): list (LString.t):=
match str with 
| head :: tail => 
    if is_prefix (app current_sep [head]) sep
    then 
        if list_ascii_eqb (app current_sep [head]) sep
        then split_LString' tail sep  nil nil (current_word :: acc)
        else split_LString' tail sep  ( app current_sep [head]) current_word (acc)
    else
        split_LString' tail sep  nil ((app (current_word) (app current_sep [head]))) (acc)
| nil => 
    if list_ascii_eqb (current_sep) sep
    then nil :: current_word :: acc
    else (app current_sep current_word) :: acc
    
end in 
rev(split_LString' str sep  nil nil nil)
.