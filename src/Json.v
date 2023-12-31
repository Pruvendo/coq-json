Require Import String.
Require Import Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Basics.

Require Export KeyMaps. 
Require Export CommonHelpers.
Require Export StringHelpers.
Require Import String.

Import ListNotations.

Local Open Scope list_scope.



Module StringKeySig <: KeyMaps.KeySig.
Definition key := string.
Definition eqKey := fun s1 s2 => if (string_dec s1 s2) then true else false.
Check string_dec.
Lemma eqKey_refl: forall s1 s2, eqKey s1 s2 = true <-> s1 = s2.
Proof.
 intros. split. unfold eqKey.
 remember (string_dec s1 s2). destruct s.
 auto. discriminate.
 intros. unfold eqKey. remember (string_dec s1 s2). destruct s.
 auto. unfold not in n. clear Heqs. apply n in H.
 inversion H.
Defined. 
End StringKeySig.

Module StringKeyMap := KeyMaps.KeyMap StringKeySig.
Export StringKeySig.
Export StringKeyMap.


(*transform this to module sig or variable*)
Definition JsonData := string.
Check JsonData.

Inductive json : Set :=
| json_data: JsonData -> json
| json_list : list json  -> json
| json_map: @key_map json -> json.

Module JsonNotations.
Notation "{ }" := (json_map empty): json_scope.
Infix "#" := mapkv (at level 0): json_scope.
Notation "{ k # v }" := (json_map (mapkv k v empty key json))
                                 (right associativity): json_scope.
Notation "{ kv1 , .. , kv2 }" := (json_map (kv1 .. (kv2 empty) ..))
                                 (right associativity): json_scope.
Notation "$ s" := (json_data s)
                       (at level 0, right associativity): json_scope.
Notation "' l" := (json_list l)
                  (at level 0, right associativity): json_scope.
Notation "& m" := (json_map m)
                  (at level 0, right associativity): json_scope.
End JsonNotations.




Import JsonNotations.
Local Open Scope json_scope.
Delimit Scope json_scope with json.

Check String.concat.
Eval compute in (substring 0 1 """").

Fixpoint json_pprint (j: json) : string :=
match j with
| json_data s => ("""" ++ s ++ """")%string
| json_list l => let ls := map json_pprint l in
                 ("[" ++ (String.concat "," ls) ++ "]" )%string
| json_map m =>  let fix iter_map m :=
                 match m with 
                 | empty => ""%string
                 | mapkv k v empty => ("""" ++ k ++ """"++": " ++ json_pprint v)%string
                 | mapkv k v m' => ("""" ++ k ++ """"++": " ++ json_pprint v ++ "," ++ (iter_map m'))%string
                 end in
                 ("{" ++ (iter_map m) ++ "}")%string
end.

(* Eval compute in (json_pprint '[ $"bar"; {"foo" # $"baz"}]). *)

Definition jsonmap (f: json -> json) (j: json) :=
match j with
| $ _ => f j
| 'l => ' (map f l)
| & m => & (mapmap f m)
end.


Definition jpoint: Set := key + nat.
Definition jpath:= list jpoint.

Check jpoint.

Fixpoint json_get (kk: jpoint) (j: json) {struct j}: option json :=
match kk with
| inl k => match j with
              | & m  => mlookup m k
              | _ => None
           end
| inr k => match j with
              | ' l  => nth_error l k
              | _ => None
           end
end.

Definition json1 := { "foo"%string # $"Andy"%string}.
(* Compute json_get (inl "foo"%string)(json1). *)

Fixpoint json_getin (lk: jpath) (j: json): option json :=
match lk with
| [] => Some j
| k::ks => let mj' := json_get k j in
           match mj' with
           | None => None
           | Some j' => json_getin ks j'
           end 
end.

Local Open Scope string_scope.

Compute json_getin([inl "bar"])(json1).

Fixpoint keymap_list (m: key_map) : list json :=
match m with
| empty => []
| mapkv k v kvs => v::(keymap_list kvs)
end.

(* Definition map1 := mapkv ("q") ({ }) empty. *)

(* Check map1. *)
(* Check keymap_list(map1). *)
(* Check eqb. *)

Fixpoint find' (k: jpoint) (l: list (nat*option jpoint)) : option nat :=
match l with
| [] => None
| (n,k')::ks => match k, k' with
          | inl a, Some (inl b) => if (string_dec a b) then Some n else (find' k ks)
          | inr a, Some (inr b) => if (Nat.eqb a b) then Some n else (find' k ks)
          | _, _ => find' k ks
          end
end.

(* return index of k(jpoint) in l(list jpoint) *)
Definition find k l := find' k (indexate l).


Check find.

(* Eval compute in (find (inr 4) [None; None; Some (inl "foo"); Some (inr 4)]). *)
(* Eval compute in (find (inl "foo") [None; None; Some (inl "foo"); Some (inr 4)]). *)
(* Eval compute in (find (inr 14) [None; None; Some (inl "foo"); Some (inr 4)]). *)

(* Compute find (inr 4) [None; Some(inr 4)]. *)

(* String -> jpoint *)
Definition from_string (s: string) : jpoint :=
if (prefix "#" s) then 
let mk := num_of_string (substring 1 (String.length s -1) s) in
match mk with
| Some k => inr k
| None => inl s
end
else inl s.



(* Eval compute in (from_string "#4"). *)
(* Eval compute in (from_string "#4t"). *)
(* Eval compute in (from_string ""). *)
(* Eval compute in (from_string "foo"). *)


Definition writeJPoint (p: jpoint) : string :=
match p with
| inr k => indexNat k
| inl k => k
end.

Compute writeJPoint((inr 4)).

Section json_ind'.

Check json_ind.

Variable P: json -> Prop.

Hypothesis json_data_case : forall (dj : JsonData),
    P (json_data dj).

Hypothesis json_list_case : forall (lj : list json),
    Forall P lj -> P (json_list lj).

Hypothesis json_map_case : forall (mj : @key_map json),
    Forall P (keymap_list mj) -> P (json_map mj).

Fixpoint json_ind' (j : json) : P j :=
match j return (P j) with
| $s => json_data_case  s
| ' lj => json_list_case lj
        ((fix json_list_ind (lj : list json) : Forall P lj :=
          match lj with
            | [] => Forall_nil P
            | j::ljx => @Forall_cons json P j ljx (json_ind' j) (json_list_ind ljx)
          end) lj)
| & mj => json_map_case mj
        ((fix json_map_ind (mj : @key_map json) : Forall P (keymap_list mj) :=
          match mj with
            | empty => Forall_nil P
            | mapkv k v mjx => @Forall_cons json P v (keymap_list mjx) (json_ind' v) (json_map_ind mjx)
          end) mj)
end.


End json_ind'.



(*tests*)

Check ($"foo").
(* Compute json_pprint(($"foo")). *)
Check {"foo" # $"bar"}.
(* Compute json_pprint({"foo" # $"bar"}). *)
Check ('([$"foo"]%list)).
(* Compute json_pprint('([$"foo"]%list)). *)
Check {"1" # $"Andy" , "2" # $"Peter"}.
(* Compute json_pprint({"1" # $"Andy" , "2" # $"Peter"}). *)
(* Compute json_pprint(json1). *)
Definition json2 := '[$"Andy"; $"Peter"].

(* Compute in (jsonmap (fun x => {}) {"foo" # $"foo", "bar" # $"bar"}). *)

Example json_get1: json_get (inl "foo") json1 = Some $"Andy".
Proof. auto. Qed.

Example json_get3: json_get (inl "baz") json1 = None.
Proof. auto. Qed.

Example json_get4: json_get (inr 0) json2 = Some $"Andy".
Proof. auto. Qed.

Example json_get5: json_get (inr 1) json2 = Some $"Peter".
Proof. auto. Qed.

Example json_get6: json_get (inr 2) json2 = None.
Proof. auto. Qed.

Example json_getin1:  json_getin [inl "foo"; inr 1] {"foo" # json2} = Some $"Peter".
Proof. auto. Qed.


Lemma json_get1_data_none: forall k s, json_get (inr k) $s = None.
Proof.
 intros. simpl. auto. Qed.

Lemma json_get2_data_none: forall k s, json_get (inl k) $s = None.
Proof.
 intros. simpl. auto. Qed.

Definition json5 := {"foo" # $"Andy", "bar" #  $"Peter"}.

Definition getJSON(o: option json): json :=
  match o with
    | Some a => a
    | None => { }
  end.

Definition getString(o: option json): string :=
  match getJSON(o) with
  | json_data s => s
  | others => ""
  end.
