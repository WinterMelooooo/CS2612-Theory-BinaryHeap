From SimpleC.ASRT Require Import DefFiles.
From SimpleC.Common Require Import CTypes.
From SimpleC.Common Require Import COps.
From SimpleC.CoreLang Require Import CTypes.
From SimpleC.CSE Require Import Cexpr_def Cstate_def Cexpr_val_helper.
From compcert.lib Require Import Coqlib Integers.

Require SimpleC.SL.SeparationLogic.
Import SeparationLogic.CRules.

Section list_denote.

Variable eval_Cexprval_denote : Cexpr -> prog_state -> val -> prog_state -> Prop.

Fixpoint eval_Cexprval_list_denote (x : list Cexpr) (Pre : prog_state) (l : list val) (Post : prog_state) : Prop :=
  match x with
    | nil =>  l = nil /\ state_eq Pre Post
    | x' :: l' => exists v Post' l2 , eval_Cexprval_denote x' Pre v Post' /\ 
                   l = v :: l2 /\ eval_Cexprval_list_denote l' Post' l2 Post  
  end. 
End list_denote.

Section Eval_semantics.

Variable env : prog_env.
Variable callees: val -> prog_state -> list val -> prog_state -> val -> Prop.

Definition const_denote
           (z: Z)(t : SimpleCtype)
           (n: val): Prop :=
  match t with 
    | CT_basic (CT_int s i) =>
        match s, i with
        | Signed, I8 => n = (Vchar (Byte.repr z))
        | Unsigned, I8 => n = (Vuchar (Byte.repr z))
        | Signed, I32 => n = (Vint (Int.repr z))
        | Unsigned, I32 => n = (Vuint (Int.repr z))
        | Signed, I64 => n = (Vlong (Int64.repr z))
        | Unsigned, I64 => n = (Vulong (Int64.repr z))
        | _, _ => False
        end /\ z <= max_int s i /\
               z >= min_int s i
    | _ => False 
  end. 

Fixpoint eval_id_addr (l : list (ident -> option (int64 * SimpleCtype))) (id : ident) : option int64 :=
  match l with 
    | nil => None 
    | a0 :: l' => match a0 id with 
                    | None => eval_id_addr l' id 
                    | Some addr => Some (fst addr)
                  end
  end.
      
Definition var_denote
           (id: var_name) (t: SimpleCtype)
           (s: prog_state)
           (n: val) :=
 exists addr, eval_id_addr ((vars_addr s) :: nil) (fst id) = Some addr /\  
 Merge_mem addr t s = Some n.

Definition deref_denote
             (v_addr : val) (t : SimpleCtype)
             (pre: prog_state)
             (v : val) : Prop :=
  match v_addr with 
    | Vulong u => Merge_mem u t pre = Some v
    | _ => False 
  end.

Definition cast_val (v : val) (t1 t2 : SimpleCtype) : option val :=
  match t1 , v with                           
    | CT_basic (CT_int Signed I8) , Vchar u => 
       match t2 with 
        | CT_basic (CT_int Signed I8) => Some (Vchar u)
        | CT_basic (CT_int Unsigned I8) => Some (Vuchar u)
        | CT_basic (CT_int Signed I32) => Some (Vint (Int.repr (Byte.signed u)))
        | CT_basic (CT_int Unsigned I32) => Some (Vuint (Int.repr (Byte.signed u)))
        | CT_basic (CT_int Signed I64) => Some (Vlong (Int64.repr (Byte.signed u)))
        | CT_basic (CT_int Unsigned I64) => Some (Vulong (Int64.repr (Byte.signed u))) 
        | _ => None 
       end
    | CT_basic (CT_int Unsigned I8) , Vuchar u => 
       match t2 with 
        | CT_basic (CT_int Signed I8) => Some (Vchar u)
        | CT_basic (CT_int Unsigned I8) => Some (Vuchar u)
        | CT_basic (CT_int Signed I32) => Some (Vint (Int.repr (Byte.unsigned u)))
        | CT_basic (CT_int Unsigned I32) => Some (Vuint (Int.repr (Byte.unsigned u)))
        | CT_basic (CT_int Signed I64) => Some (Vlong (Int64.repr (Byte.unsigned u)))
        | CT_basic (CT_int Unsigned I64) => Some (Vulong (Int64.repr (Byte.unsigned u))) 
        | _ => None 
       end
    | CT_basic (CT_int Signed I32) , Vint u => 
       match t2 with 
        | CT_basic (CT_int Signed I8) => None 
        | CT_basic (CT_int Unsigned I8) => None 
        | CT_basic (CT_int Signed I32) => Some (Vint u)
        | CT_basic (CT_int Unsigned I32) => Some (Vuint u)
        | CT_basic (CT_int Signed I64) => Some (Vlong (Int64.repr (Int.signed u)))
        | CT_basic (CT_int Unsigned I64) => Some (Vulong (Int64.repr (Int.signed u))) 
        | _ => None 
       end
    | CT_basic (CT_int Unsigned I32) , Vuint u => 
       match t2 with 
        | CT_basic (CT_int Signed I8) => None 
        | CT_basic (CT_int Unsigned I8) => None 
        | CT_basic (CT_int Signed I32) => Some (Vint u)
        | CT_basic (CT_int Unsigned I32) => Some (Vuint u)
        | CT_basic (CT_int Signed I64) => Some (Vlong (Int64.repr (Int.unsigned u)))
        | CT_basic (CT_int Unsigned I64) => Some (Vulong (Int64.repr (Int.unsigned u))) 
        | _ => None 
       end
    | CT_basic (CT_int Signed I64) , Vlong u => 
       match t2 with 
        | CT_basic (CT_int Signed I8) => None 
        | CT_basic (CT_int Unsigned I8) => None 
        | CT_basic (CT_int Signed I32) => None 
        | CT_basic (CT_int Unsigned I32) => None 
        | CT_basic (CT_int Signed I64) => Some (Vlong u)
        | CT_basic (CT_int Unsigned I64) => Some (Vulong u) 
        | _ => None 
       end
    | CT_basic (CT_int Unsigned I64) , Vulong u => 
       match t2 with 
        | CT_basic (CT_int Signed I8) => None 
        | CT_basic (CT_int Unsigned I8) => None 
        | CT_basic (CT_int Signed I32) => None 
        | CT_basic (CT_int Unsigned I32) => None 
        | CT_basic (CT_int Signed I64) => Some (Vlong u)
        | CT_basic (CT_int Unsigned I64) => Some (Vulong u) 
        | _ => None 
       end
    | _ , _ => None  
  end.

Definition neg_denote
             (v': val)
             (s: prog_state)
             (v : val): Prop :=
  match v' with 
    | Vint u => v = Vint (Int.neg u) /\ Int.signed u <> Int.min_signed
    | Vlong u => v = Vlong (Int64.neg u) /\ Int64.signed u <> Int64.min_signed 
    | Vchar u => v = Vchar (Byte.neg u) /\ Byte.signed u <> Byte.min_signed
    | _ => False
  end. 


Definition notbool_denote
             (v': val)
             (s: prog_state)
             (v : val): Prop :=
  match v' with 
    | Vint u => (u = Int.repr 0 /\ v = Vint (Int.repr 1)) \/ 
                    (u <> Int.repr 0 /\ v = Vint (Int.repr 0))
    | Vuint u => (u = Int.repr 0 /\ v = Vuint (Int.repr 1)) \/ 
                    (u <> Int.repr 0 /\ v = Vuint (Int.repr 0))
    | Vlong u => (u = Int64.repr 0 /\ v = Vlong (Int64.repr 1)) \/ 
                    (u <> Int64.repr 0 /\ v = Vlong (Int64.repr 0))
    | Vulong u => (u = Int64.repr 0 /\ v = Vulong (Int64.repr 1)) \/ 
                    (u <> Int64.repr 0 /\ v = Vulong (Int64.repr 0)) 
    | Vchar u => (u = Byte.repr 0 /\ v = Vuchar (Byte.repr 1)) \/ 
                    (u <> Byte.repr 0 /\ v = Vuchar (Byte.repr 0))
    | Vuchar u => (u = Byte.repr 0 /\ v = Vuchar (Byte.repr 1)) \/ 
                    (u <> Byte.repr 0 /\ v = Vuchar (Byte.repr 0))
  end.

Definition notint_denote
             (v': val)
             (s: prog_state)
             (v : val): Prop :=
  match v' with 
    | Vint u => v = Vint (Int.not u)
    | Vuint u => v = Vuint (Int.not u)
    | Vlong u => v = Vlong (Int64.not u)
    | Vulong u => v = Vulong (Int64.not u) 
    | Vchar u => v = Vchar (Byte.not u)
    | Vuchar u => v = Vuchar (Byte.not u)
  end.
  
Definition Unop_denote (op : CUop) (v' : val) (Post : prog_state) (v : val) : Prop :=
  match op with
    | CO_NOTINT => notint_denote v' Post v
    | CO_NOTBOOL => notbool_denote v' Post v 
    | CO_UMINUS => neg_denote v' Post v 
    | CO_UPLUS => v' = v
  end.

Definition arith_denote1 (t : SimpleCtype)
             (valfun: val -> val -> option val)
             (v1 v2 v : val) : Prop :=
  valfun v1 v2 = Some v /\ exists n , const_denote n t v.

Definition arith_denote2 (t : SimpleCtype)
             (valfun: val -> val -> option val)
             (v1 v2 v : val) : Prop :=
  valfun v1 v2 = Some v /\ exists n , const_denote n t v /\
    Some v2 <> Zero t /\ (Some v1 <> Signed_min t \/ Some v2 <> Minus1 t).

Definition cmp_denote
     (c: comparison) (t : SimpleCtype)
     (v1 v2 v : val) : Prop :=
  exists n , Some n = val_cmp c v1 v2 /\ 
      const_denote (Z.b2z n) t v.

Definition and_denote (t : SimpleCtype) (v1 v2 v : val) (P : Prop) : Prop :=
  (Some v1 = Zero t /\ Some v = Zero t) \/  
  (Some v1 <> Zero t /\ v = v2 /\ P).

Definition or_denote (t : SimpleCtype) (v1 v2 v : val) (P : Prop) : Prop :=
  (Some v1 <> Zero t /\ Some v = One t) \/  
  (Some v1 = Zero t /\ v = v2 /\ P).

Definition Binop_denote (op : CBinop) (t : SimpleCtype) (v1 v2 v : val) (P : Prop) : Prop :=
  match op with
    | CO_PLUS => arith_denote1 t val_add v1 v2 v /\ P
    | CO_MINUS => arith_denote1 t val_sub v1 v2 v /\ P 
    | CO_MUL => arith_denote1 t val_mul v1 v2 v /\ P 
    | CO_DIV => arith_denote2 t val_div v1 v2 v /\ P  
    | CO_MOD => arith_denote2 t val_mod v1 v2 v /\ P 
    | CO_AND => arith_denote1 t val_and v1 v2 v /\ P  
    | CO_OR => arith_denote1 t val_or v1 v2 v /\ P
    | CO_XOR => arith_denote1 t val_xor v1 v2 v /\ P
    | CO_SHL => arith_denote1 t val_shl v1 v2 v /\ P
    | CO_SHR => arith_denote1 t val_shr v1 v2 v /\ P 
    | CO_EQ => cmp_denote Ceq t v1 v2 v /\ P 
    | CO_NE => cmp_denote Cne t v1 v2 v /\ P
    | CO_LT => cmp_denote Clt t v1 v2 v /\ P 
    | CO_GT => cmp_denote Cgt t v1 v2 v /\ P 
    | CO_LE => cmp_denote Cle t v1 v2 v /\ P 
    | CO_GE => cmp_denote Cge t v1 v2 v /\ P
    | CO_BAND => and_denote t v1 v2 v P
    | CO_BOR => or_denote t v1 v2 v P 
  end.

Fixpoint eval_Cexprval_denote (x : Cexpr) (Pre : prog_state) (v : val) (Post : prog_state) : Prop :=
  match x with
  | C_const i t => const_denote i t v /\ state_eq Pre Post
  | C_var id t => var_denote id t Pre v /\ state_eq Pre Post
  | C_deref x' t => exists v' , eval_Cexprval_denote x' Pre v' Post /\ deref_denote v' t Post v
  | C_addrof x' t => exists v' , eval_Cexprval_l_denote x' Pre v' Post /\ v = (Vulong v')
  | C_unop op x' t => exists v', eval_Cexprval_denote x' Pre v' Post /\ Unop_denote op v' Post v
  | C_binop op x1 x2 t => exists v1 Post', eval_Cexprval_denote x1 Pre v1 Post' /\
                            exists v2 , Binop_denote op t v1 v2 v (eval_Cexprval_denote x2 Post' v2 Post)
  | C_cast x t => exists v', eval_Cexprval_denote x Pre v' Post /\ cast_val v' (type_of x) t = Some v 
  | C_call f args t => exists v' Post', eval_Cexprval_denote f Pre v' Post' /\ 
                       exists l Post'' , eval_Cexprval_list_denote eval_Cexprval_denote args Post' l Post'' /\
                       callees v' Post'' l Post v
  | C_structfield x' id1 id2 t => exists v', eval_Cexprval_l_denote x' Pre v' Post /\ 
                               exists m, (struct_pos env) v' id2 = Some m /\     
                                  Some v = Merge_mem m t Post /\ exists p , const_denote p t v
  | C_unionfield x' id1 id2 t => exists v', eval_Cexprval_l_denote x' Pre v' Post /\ 
                               exists m, (union_pos env) v' id2 = Some m /\     
                                  Some v = Merge_mem m t Post /\ exists p , const_denote p t v
  | C_index a n t => exists v' Post', eval_Cexprval_l_denote a Pre v' Post' /\
                       exists n', eval_Cexprval_denote n Post' n' Post /\
                         exists m p, n' = Vulong m /\ Int64.add v' (Int64.mul m (Int64.repr (Ctype_size t))) = Int64.repr p /\ p >= 0 /\ p <= Int64.max_unsigned /\ Some v = Merge_mem (Int64.repr p) t Post
  | C_sizeof x t => const_denote (Ctype_size x) t v /\ state_eq Pre Post
  end
  
with eval_Cexprval_l_denote (x : Cexpr) (Pre : prog_state) (v : int64) (Post : prog_state) : Prop :=
  match x with
  | C_var id t => Some v = eval_id_addr ((vars_addr Pre)::nil) (fst id) /\ state_eq Pre Post 
  | C_deref x' t => eval_Cexprval_denote x' Pre (Vulong v) Post
  | C_structfield x' id1 id2 t => exists v', eval_Cexprval_l_denote x' Pre v' Post /\ 
                              exists m , (struct_pos env) v' id2 = Some v /\     
                                  v = Int64.repr m /\ m <= Int64.max_unsigned /\ m >= 0
  | C_unionfield x' id1 id2 t => exists v', eval_Cexprval_l_denote x' Pre v' Post /\ 
                               exists m , (union_pos env) v' id2 = Some v /\     
                                  v = Int64.repr m /\ m <= Int64.max_unsigned /\ m >= 0
  | C_index a n t => exists v' Post', eval_Cexprval_l_denote a Pre v' Post' /\
                       exists n', eval_Cexprval_denote n Post' n' Post /\
                         exists m p,  n' = Vulong m /\ 
                              v = Int64.add v' (Int64.mul m (Int64.repr (Ctype_size t))) /\ 
                              v = Int64.repr p /\  p >= 0 /\ p <= Int64.max_unsigned 
  | _ => False 
  end.

End Eval_semantics.
