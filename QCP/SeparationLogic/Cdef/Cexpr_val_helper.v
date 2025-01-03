From SimpleC.ASRT Require Import DefFiles.
From SimpleC.Common Require Import CTypes.
From SimpleC.CoreLang Require Import CTypes.
From SimpleC.CSE Require Import Cexpr_def Cstate_def.
From SimpleC.SL Require Mem.
From compcert.lib Require Import Coqlib Integers.

Definition Zero (t : SimpleCtype) :=
  match t with 
    | CT_basic (CT_int Signed I8) => Some (Vchar (Byte.repr 0))
    | CT_basic (CT_int Unsigned I8) => Some (Vuchar (Byte.repr 0))
    | CT_basic (CT_int Signed I32) => Some (Vint (Int.repr 0)) 
    | CT_basic (CT_int Unsigned I32) => Some (Vuint (Int.repr 0)) 
    | CT_basic (CT_int Signed I64) => Some (Vlong (Int64.repr 0)) 
    | CT_basic (CT_int Unsigned I64) => Some (Vulong (Int64.repr 0))  
    | _ => None 
  end.

Definition One (t : SimpleCtype) :=
  match t with 
    | CT_basic (CT_int Signed I8) => Some (Vchar (Byte.repr 1))
    | CT_basic (CT_int Unsigned I8) => Some (Vuchar (Byte.repr 1))
    | CT_basic (CT_int Signed I32) => Some (Vint (Int.repr 1)) 
    | CT_basic (CT_int Unsigned I32) => Some (Vuint (Int.repr 1)) 
    | CT_basic (CT_int Signed I64) => Some (Vlong (Int64.repr 1)) 
    | CT_basic (CT_int Unsigned I64) => Some (Vulong (Int64.repr 1))  
    | _ => None 
  end.

Definition Signed_min (t : SimpleCtype) :=
  match t with 
    | CT_basic (CT_int Signed I8) => Some (Vchar (Byte.repr Byte.min_signed))
    | CT_basic (CT_int Signed I32) => Some (Vint (Int.repr Int.min_signed))  
    | CT_basic (CT_int Signed I64) => Some (Vlong (Int64.repr Int.min_signed))   
    | _ => None
  end.

Definition Minus1 (t : SimpleCtype) :=
  match t with 
    | CT_basic (CT_int Signed I8) => Some (Vchar (Byte.repr (-1)))
    | CT_basic (CT_int Signed I32) => Some (Vint (Int.repr (-1)))
    | CT_basic (CT_int Signed I64) => Some (Vlong (Int64.repr (-1)))
    | _ => None 
  end.

(* Fixpoint Eval_from_state (pos : Mem.addr) (now_val : Z) (num : nat) (state : prog_state) : option Z :=
  match num with 
    | O => Some now_val 
    | S n => match (state.(mem) pos) with 
               | Mem.value i => Eval_from_state (pos + 1) (now_val * 32 + i) n state   
               | _ => None 
             end
  end.

Definition Merge_mem (pos : int64) (t : SimpleCtype) (state : prog_state) : option val := 
  match t with 
    | CT_basic (CT_int Unsigned I8) =>
                       match Eval_from_state pos 0 1 state with 
                         | None => None 
                         | Some z => Some (Vuchar (Byte.repr z)) 
                       end
    | CT_basic (CT_int Signed I8) =>
                     match Eval_from_state pos 0 1 state with 
                       | None => None 
                       | Some z => Some (Vchar (Byte.repr z)) 
                     end
    | CT_basic (CT_int Unsigned I32) =>
                       match Eval_from_state pos 0 4 state with 
                         | None => None 
                         | Some z => Some (Vuint (Int.repr z)) 
                       end
    | CT_basic (CT_int Signed I32) =>
                       match Eval_from_state pos 0 4 state with 
                        | None => None 
                        | Some z => Some (Vint (Int.repr z)) 
                       end
    | CT_basic (CT_int Signed I64) =>
                          match Eval_from_state pos 0 8 state with 
                            | None => None 
                            | Some z => Some (Vlong (Int64.repr z)) 
                          end
    | CT_basic (CT_int Unsigned I64) =>
                          match Eval_from_state pos 0 8 state with 
                            | None => None 
                            | Some z => Some (Vulong (Int64.repr z)) 
                          end
    | _ => None 
  end.

Fixpoint Load_into_state (pos : int64) (num : nat) (v : Z) (state : prog_state) : prog_state :=
  match num with  
    | O => state 
    | S n => Load_into_state pos n (v / 32) (mk_progstate (state.(vars_addr)) (fun a => if (Int64.cmp Ceq a (Int64.add pos (Int64.repr (Z.of_nat  n)))) then value (Byte.repr (v mod 32)) else (state.(mem) a)))
  end.

Definition Split_mem (pos : int64) (v : val) (state : prog_state) : prog_state :=
  match v with 
    | Vuchar b => Load_into_state pos 1 (Byte.unsigned b) state 
    | Vchar b => Load_into_state pos 1 (Byte.unsigned b) state
    | Vuint b => Load_into_state pos 4 (Int.unsigned b) state 
    | Vint b => Load_into_state pos 4 (Int.unsigned b) state
    | Vlong b => Load_into_state pos 8 (Int64.unsigned b) state
    | Vulong b => Load_into_state pos 8 (Int64.unsigned b) state
  end. *)

Definition val_add (a b : val) : option val :=
  match a , b with 
    | Vint a0 , Vint b0 => Some (Vint (Int.add a0 b0))
    | Vuint a0 , Vuint b0 => Some (Vuint (Int.add a0 b0))
    | Vchar a0 , Vchar b0 => Some (Vchar (Byte.add a0 b0))
    | Vuchar a0 , Vuchar b0 => Some (Vuchar (Byte.add a0 b0))
    | Vlong a0 , Vlong b0 => Some (Vlong (Int64.add a0 b0))
    | Vulong a0 , Vulong b0 => Some (Vulong (Int64.add a0 b0))
    | _ , _ => None 
  end.

Definition val_sub (a b : val) : option val :=
  match a , b with 
    | Vint a0 , Vint b0 => Some (Vint (Int.sub a0 b0))
    | Vuint a0 , Vuint b0 => Some (Vuint (Int.sub a0 b0))
    | Vchar a0 , Vchar b0 => Some (Vchar (Byte.sub a0 b0))
    | Vuchar a0 , Vuchar b0 => Some (Vuchar (Byte.sub a0 b0))
    | Vlong a0 , Vlong b0 => Some (Vlong (Int64.sub a0 b0))
    | Vulong a0 , Vulong b0 => Some (Vulong (Int64.sub a0 b0))
    | _ , _ => None
  end.

Definition val_mul (a b : val) : option val :=
  match a , b with 
    | Vint a0 , Vint b0 => Some (Vint (Int.mul a0 b0))
    | Vuint a0 , Vuint b0 => Some (Vuint (Int.mul a0 b0))
    | Vchar a0 , Vchar b0 => Some (Vchar (Byte.mul a0 b0))
    | Vuchar a0 , Vuchar b0 => Some (Vuchar (Byte.mul a0 b0))
    | Vlong a0 , Vlong b0 => Some (Vlong (Int64.mul a0 b0))
    | Vulong a0 , Vulong b0 => Some (Vulong (Int64.mul a0 b0))
    | _ , _ => None
  end.

Definition val_div (a b : val) : option val :=
  match a , b with 
    | Vint a0 , Vint b0 => Some (Vint (Int.divs a0 b0))
    | Vuint a0 , Vuint b0 => Some (Vuint (Int.divs a0 b0))
    | Vchar a0 , Vchar b0 => Some (Vchar (Byte.divs a0 b0))
    | Vuchar a0 , Vuchar b0 => Some (Vuchar (Byte.divs a0 b0))
    | Vlong a0 , Vlong b0 => Some (Vlong (Int64.divs a0 b0))
    | Vulong a0 , Vulong b0 => Some (Vulong (Int64.divs a0 b0))
    | _ , _ => None
  end.

Definition val_mod (a b : val) : option val :=
  match a , b with 
    | Vint a0 , Vint b0 => Some (Vint (Int.mods a0 b0))
    | Vuint a0 , Vuint b0 => Some (Vuint (Int.mods a0 b0))
    | Vchar a0 , Vchar b0 => Some (Vchar (Byte.mods a0 b0))
    | Vuchar a0 , Vuchar b0 => Some (Vuchar (Byte.mods a0 b0))
    | Vlong a0 , Vlong b0 => Some (Vlong (Int64.mods a0 b0))
    | Vulong a0 , Vulong b0 => Some (Vulong (Int64.mods a0 b0))
    | _ , _ => None
  end.

Definition val_and (a b : val) : option val :=
  match a , b with 
    | Vint a0 , Vint b0 => Some (Vint (Int.and a0 b0))
    | Vuint a0 , Vuint b0 => Some (Vuint (Int.and a0 b0))
    | Vchar a0 , Vchar b0 => Some (Vchar (Byte.and a0 b0))
    | Vuchar a0 , Vuchar b0 => Some (Vuchar (Byte.and a0 b0))
    | Vlong a0 , Vlong b0 => Some (Vlong (Int64.and a0 b0))
    | Vulong a0 , Vulong b0 => Some (Vulong (Int64.and a0 b0))
    | _ , _ => None
  end.

Definition val_or (a b : val) : option val :=
  match a , b with 
    | Vint a0 , Vint b0 => Some (Vint (Int.or a0 b0))
    | Vuint a0 , Vuint b0 => Some (Vuint (Int.or a0 b0))
    | Vchar a0 , Vchar b0 => Some (Vchar (Byte.or a0 b0))
    | Vuchar a0 , Vuchar b0 => Some (Vuchar (Byte.or a0 b0))
    | Vlong a0 , Vlong b0 => Some (Vlong (Int64.or a0 b0))
    | Vulong a0 , Vulong b0 => Some (Vulong (Int64.or a0 b0))
    | _ , _ => None
  end.

Definition val_xor (a b : val) : option val :=
  match a , b with 
    | Vint a0 , Vint b0 => Some (Vint (Int.xor a0 b0))
    | Vuint a0 , Vuint b0 => Some (Vuint (Int.xor a0 b0))
    | Vchar a0 , Vchar b0 => Some (Vchar (Byte.xor a0 b0))
    | Vuchar a0 , Vuchar b0 => Some (Vuchar (Byte.xor a0 b0))
    | Vlong a0 , Vlong b0 => Some (Vlong (Int64.xor a0 b0))
    | Vulong a0 , Vulong b0 => Some (Vulong (Int64.xor a0 b0))
    | _ , _ => None
  end.

Definition val_shl (a b : val) : option val :=
  match a , b with 
    | Vint a0 , Vint b0 => Some (Vint (Int.shl a0 b0))
    | Vuint a0 , Vuint b0 => Some (Vuint (Int.shl a0 b0))
    | Vchar a0 , Vchar b0 => Some (Vchar (Byte.shl a0 b0))
    | Vuchar a0 , Vuchar b0 => Some (Vuchar (Byte.shl a0 b0))
    | Vlong a0 , Vlong b0 => Some (Vlong (Int64.shl a0 b0))
    | Vulong a0 , Vulong b0 => Some (Vulong (Int64.shl a0 b0))
    | _ , _ => None
  end.

Definition val_shr (a b : val) : option val :=
  match a , b with 
    | Vint a0 , Vint b0 => Some (Vint (Int.shr a0 b0))
    | Vuint a0 , Vuint b0 => Some (Vuint (Int.shr a0 b0))
    | Vchar a0 , Vchar b0 => Some (Vchar (Byte.shr a0 b0))
    | Vuchar a0 , Vuchar b0 => Some (Vuchar (Byte.shr a0 b0))
    | Vlong a0 , Vlong b0 => Some (Vlong (Int64.shr a0 b0))
    | Vulong a0 , Vulong b0 => Some (Vulong (Int64.shr a0 b0))
    | _ , _ => None
  end.

Definition val_cmp (cp : comparison) (a b : val) : option bool :=
  match a , b with 
    | Vint a0 , Vint b0 => Some (Int.cmp cp a0 b0)
    | Vuint a0 , Vuint b0 => Some (Int.cmp cp a0 b0)
    | Vchar a0 , Vchar b0 => Some (Byte.cmp cp a0 b0)
    | Vuchar a0 , Vuchar b0 => Some (Byte.cmp cp a0 b0)
    | Vlong a0 , Vlong b0 => Some (Int64.cmp cp a0 b0)
    | Vulong a0 , Vulong b0 => Some (Int64.cmp cp a0 b0)
    | _ , _ => None
  end.