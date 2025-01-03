(** this file contains the definition of error message *)
From SimpleC.ASRTFUN Require Import list_lemma.
From compcert.lib Require Import Coqlib.

Inductive Error_message : Type :=
  | Div_zero : Error_message 
  | Memory_leak : Error_message
  | Invalid_load : Error_message
  | Invalid_store : Error_message
  | Invalid_operation : Error_message 
  | Invalid_call : Error_message
  | Nofuncdef : Error_message
  | Time_out : Error_message
.

Inductive Error : Type :=
  | ok : Error
  | error : Error_message -> Error
.

Definition message_string (E : Error_message) : string :=
  match E with
    | Div_zero => "divide zero"
    | Memory_leak => "memory leak"
    | Invalid_load => "Invalid load"
    | Invalid_store => "Invalid store"
    | Invalid_operation => "Invalid operation"
    | Invalid_call => "Invalid_call"
    | Time_out => "Time out"
    | Nofuncdef => "No function definition"
  end.


Definition Error_string (e : Error) : string :=
  match e with
    | ok => "no"
    | error E => message_string E
  end.

Definition error_message_eqb (a b : Error_message) : bool :=
  match a , b with
    | Div_zero , Div_zero => true
    | Memory_leak, Memory_leak => true
    | Invalid_load, Invalid_load => true
    | Invalid_store, Invalid_store => true
    | Invalid_operation, Invalid_operation => true
    | Time_out, Time_out => true
    | Invalid_call , Invalid_call => true
    | Nofuncdef , Nofuncdef => true
    | _ , _ => false
  end.

Definition error_eqb (a b : Error) : bool :=
  match a , b with
    | ok , ok => true
    | error A , error B => error_message_eqb A B
    | _ , _ => false
  end.