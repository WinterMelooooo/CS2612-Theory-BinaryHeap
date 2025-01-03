Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import ExtLib.Structures.Monad. Import MonadNotation.
Require Import SetsClass.SetsClass. Import SetsNotation. Import ListConn.
Require Import SimpleC.Common.CTypes.
Require Import SimpleC.Frontend.CTypes.
Require Import SimpleC.CoreLang.CTypes.
Require Import SimpleC.CoreLang.CTypesDefDeclSem.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope monad_scope.
Local Open Scope sets.
Local Open Scope list.

Definition foldM {M: Type -> Type} {MD: Monad M} {T} (l: list (M T)):
  M (list T) :=
  fold_right
    (fun a res =>
       t <- a;;
       ts <- res;;
       ret (cons t ts))
    (ret nil)
    l.

Inductive AbortCases (E U I: Type): Type :=
| Error (x: E)
| Unsupported (x: U)
| Impossible (x: I).

Arguments Error {E} {U} {I} (x).
Arguments Unsupported {E} {U} {I} (x).
Arguments Impossible {E} {U} {I} (x).

Definition CheckResult (E U I: Type): Type :=
  option (AbortCases E U I).

Notation "'Legal'" := (@None (AbortCases _ _ _)) (at level 0).

Inductive CTypeType: Type :=
  | C_Struct
  | C_Union
  | C_Enum.

Inductive ImpossibleCases: Type :=
  | NoNameNoField (T: CTypeType)
  | UnknownAliasType.

Inductive ErrorMsg: Type :=
  | UsedDiffFromDeclared (T1 T2: CTypeType)
      (** use as T1, declared as T2, T1 <> T2 *)
  | DefinedDiffFromDeclared (T1 T2: CTypeType)
      (** defined as T1, declared as T2, T1 <> T2 *)
  | DefinedTwice (T1 T2: CTypeType)
      (** defined first time as T1, second time as T2 *)
  | DeclaredTwiceDifferently (T1 T2: CTypeType)
      (** declared first time as T1, second time as T2, T1 <> T2 *)
  | ArrayElementIsDynamicArray
  | StructFieldIsDynamicArray_ExceptTheLastOne
  | UnionFieldIsDynamicArray
  | FieldNameConflict (T: CTypeType)
      (** T <> C_Enum *)
  | FieldNameConflictCausedByUnnamedField (T: CTypeType)
      (** T <> C_Enum *)
  | UnnamedFieldIsNotStructOrUnion
  | EnumeratorNameConflictInOneEnum
  | EnumeratorNameConflictInTwoEnums
  | EnumeratorConstantConflict (** We abandom this, not C standard. *)
  .

Inductive UnsupportedCases: Type :=
  | DynamicArrayInTheLastStructField.

(** 开-fms-extensions时，匿名域可以是其他方式定义的struct/union，但是依然不能是struct/union之外的类型。
    -fplan9-extensions对于unnamed fields以及类型转换有更宽松的许可条件。 *)

Record TransState: Type :=
  {
    next_id: Z;
    type_env: TypeEnv;
  }.

Record TransM T: Type :=
  {
    legal: T ->
           TransState ->
           list (TypeDecl + TypeDef) ->
           TransState ->
           Prop;
    abort: TransState ->
           list (TypeDecl + TypeDef) ->
           AbortCases
             ErrorMsg
             UnsupportedCases
             ImpossibleCases ->
           Prop
  }.

Notation "x '.(legal)'" := (legal _ x)
  (at level 1).

Notation "x '.(abort)'" := (abort _ x)
  (at level 1).

#[local] Instance TransMonad: Monad TransM :=
  {|
    ret := fun (T: Type) (t: T) =>
             {|
               legal := fun t0 => Sets.prop_inj (t0 = t) ∩ Rels.id;
               abort := ∅;
             |};
    bind := fun (T1 T2: Type) a b =>
             {|
               legal := fun t2 =>
                          ⋃ (fun t1 => a.(legal) t1 ∘ (b t1).(legal) t2);
               abort := ⋃ (fun t1 => a.(legal) t1 ∘ (b t1).(abort)) ∪
                        a.(abort);
             |}
  |}.

Definition get_and_inc: TransM Z :=
  {|
    legal := fun z s1 l s2 =>
               z = s1.(next_id) /\
               s2.(next_id) = s1.(next_id) + 1 /\
               s2.(type_env) = s1.(type_env) /\
               l = nil;
    abort := ∅;
  |}.

Definition get_level: TransM nat :=
  {|
    legal := fun n s1 l s2 =>
               n = length s1.(type_env).(rest_of_stack) /\
               s1 = s2 /\
               l = nil;
    abort := ∅;
  |}.

Definition record_TypeDecl (pp: TypeDecl): TransM unit :=
  {|
    legal := fun _ s1 l s2 =>
               s1 = s2 /\ l = [inl pp];
    abort := ∅;
  |}.

Definition record_TypeDef (pp: TypeDef): TransM unit :=
  {|
    legal := fun _ s1 l s2 =>
               s1 = s2 /\ l = [inr pp];
    abort := ∅;
  |}.

Definition report_error {T: Type} (e: ErrorMsg): TransM T :=
  {|
    legal := ∅;
    abort := fun s l a => l = nil /\ a = Error e;
  |}.

Definition report_unsupported {T: Type} (u: UnsupportedCases): TransM T :=
  {|
    legal := ∅;
    abort := fun s l a => l = nil /\ a = Unsupported u;
  |}.

Definition report_impossible {T: Type} (i: ImpossibleCases): TransM T :=
  {|
    legal := ∅;
    abort := fun s l a => l = nil /\ a = Impossible i;
  |}.

Definition is_dynamic_array (t: SimpleCtype): bool :=
  match t with
  | CT_array _ None => true
  | _ => false
  end.

Definition get_top_SUE_state s: TransM (option StructUnionEnum_State) :=
  {|
    legal := fun o s1 l s2 =>
               o = CTypesDefDeclSem.get_top_SUE_state s1.(type_env) s /\
               s1 = s2 /\
               l = nil;
    abort := ∅;
  |}.

Definition get_SUE_state s: TransM (option (StructUnionEnum_State * nat)) :=
  {|
    legal := fun o s1 l s2 =>
               o = CTypesDefDeclSem.get_SUE_state s1.(type_env) s /\
               s1 = s2 /\
               l = nil;
    abort := ∅;
  |}.

Definition get_top_alias_state s: TransM (option SimpleCtype) :=
  {|
    legal := fun o s1 l s2 =>
               o = CTypesDefDeclSem.get_top_alias_state s1.(type_env) s /\
               s1 = s2 /\
               l = nil;
    abort := ∅;
  |}.

Definition get_alias_state s: TransM (option (SimpleCtype * nat)) :=
  {|
    legal := fun o s1 l s2 =>
               o = CTypesDefDeclSem.get_alias_state s1.(type_env) s /\
               s1 = s2 /\
               l = nil;
    abort := ∅;
  |}.

Fixpoint trans_Enumerators_rec (l: list Frontend.CTypes.Enumerator) (z: Z):
  list CoreLang.CTypes.Enumerator :=
  match l with
  | nil => nil
  | {| Frontend.CTypes.enumerator_name := s;
       Frontend.CTypes.enumerator_value := Some z0; |} :: l0 =>
    {| CoreLang.CTypes.enumerator_name := s;
       CoreLang.CTypes.enumerator_value := z0; |} :: 
    trans_Enumerators_rec l0 (z0 + 1)
  | {| Frontend.CTypes.enumerator_name := s;
       Frontend.CTypes.enumerator_value := None; |} :: l0 =>
    {| CoreLang.CTypes.enumerator_name := s;
       CoreLang.CTypes.enumerator_value := z; |} :: 
    trans_Enumerators_rec l0 (z + 1)
  end.

Definition trans_Enumerators l := trans_Enumerators_rec l 0.

Fixpoint trans_LeftType (t: LeftType): TransM SimpleCtype :=
  match t with
  | CLT_basic t =>
      ret (CT_basic t)
  | CLT_alias s =>
      o <- get_alias_state s;;
      match o with
      | None => report_impossible UnknownAliasType
      | Some (_, n) => ret (CT_alias s n)
      end
  | CLT_struct None None =>
      report_impossible (NoNameNoField C_Struct)
  | CLT_struct (Some s) None =>
      o <- get_SUE_state s;;
      match o with
      | None =>
          record_TypeDecl (CTDecl_struct s);;
          n <- get_level;;
          ret (CT_struct (CTN_named s) n)
      | Some (Declared_struct, n)
      | Some (Defined_struct _, n) =>
          ret (CT_struct (CTN_named s) n)
      | Some (Declared_union, _) =>
          report_error (DeclaredTwiceDifferently C_Union C_Struct)
      | Some (Declared_enum, _) =>
          report_error (DeclaredTwiceDifferently C_Enum C_Struct)
      | Some (Defined_union _, _) =>
          report_error (DefinedDiffFromDeclared C_Union C_Struct)
      | Some (Defined_enum _, _) =>
          report_error (DefinedDiffFromDeclared C_Enum C_Struct)
      end
  | CLT_struct (Some s) (Some l) =>
      o <- get_top_SUE_state s;;
      match o with
      | None
      | Some Declared_struct =>
          n <- get_level;;
          record_TypeDecl (CTDecl_struct s);;
          Fs <- foldM (map trans_FieldsDecl l);;
          record_TypeDef (CTDef_struct (CTN_named s) (concat Fs));;
          ret (CT_struct (CTN_named s) n)
      | Some Declared_enum =>
          report_error (DefinedDiffFromDeclared C_Struct C_Enum)
      | Some Declared_union =>
          report_error (DefinedDiffFromDeclared C_Struct C_Union)
      | Some (Defined_enum _) =>
          report_error (DefinedTwice C_Enum C_Struct)
      | Some (Defined_union _) =>
          report_error (DefinedTwice C_Union C_Struct)
      | Some (Defined_struct _) =>
          report_error (DefinedTwice C_Struct C_Struct)
      end
  | CLT_struct None (Some l) =>
      z <- get_and_inc;;
      n <- get_level;;
      Fs <- foldM (map trans_FieldsDecl l);;
      record_TypeDef (CTDef_struct (CTN_unnamed z) (concat Fs));;
      ret (CT_struct (CTN_unnamed z) n)
  | CLT_union None None =>
      report_impossible (NoNameNoField C_Union)
  | CLT_union (Some s) None =>
      o <- get_SUE_state s;;
      match o with
      | None =>
          record_TypeDecl (CTDecl_union s);;
          n <- get_level;;
          ret (CT_union (CTN_named s) n)
      | Some (Declared_union, n)
      | Some (Defined_union _, n) =>
          ret (CT_union (CTN_named s) n)
      | Some (Declared_struct, _) =>
          report_error (DeclaredTwiceDifferently C_Struct C_Union)
      | Some (Declared_enum, _) =>
          report_error (DeclaredTwiceDifferently C_Enum C_Union)
      | Some (Defined_struct _, _) =>
          report_error (DefinedDiffFromDeclared C_Struct C_Union)
      | Some (Defined_enum _, _) =>
          report_error (DefinedDiffFromDeclared C_Enum C_Union)
      end
  | CLT_union (Some s) (Some l) =>
      o <- get_top_SUE_state s;;
      match o with
      | None
      | Some Declared_union =>
          n <- get_level;;
          record_TypeDecl (CTDecl_union s);;
          Fs <- foldM (map trans_FieldsDecl l);;
          record_TypeDef (CTDef_union (CTN_named s) (concat Fs));;
          ret (CT_union (CTN_named s) n)
      | Some Declared_enum =>
          report_error (DefinedDiffFromDeclared C_Union C_Enum)
      | Some Declared_struct =>
          report_error (DefinedDiffFromDeclared C_Union C_Struct)
      | Some (Defined_enum _) =>
          report_error (DefinedTwice C_Enum C_Union)
      | Some (Defined_struct _) =>
          report_error (DefinedTwice C_Struct C_Union)
      | Some (Defined_union _) =>
          report_error (DefinedTwice C_Union C_Union)
      end
  | CLT_union None (Some l) =>
      z <- get_and_inc;;
      n <- get_level;;
      Fs <- foldM (map trans_FieldsDecl l);;
      record_TypeDef (CTDef_union (CTN_unnamed z) (concat Fs));;
      ret (CT_union (CTN_unnamed z) n)
  | CLT_enum None None =>
      report_impossible (NoNameNoField C_Enum)
  | CLT_enum (Some s) None =>
      sts <- get_SUE_state s;;
      match sts with
      | None =>
          record_TypeDecl (CTDecl_enum s);;
          n <- get_level;;
          ret (CT_enum (CTN_named s) n)
      | Some (Declared_enum, n)
      | Some (Defined_enum _, n) =>
          ret (CT_enum (CTN_named s) n)
      | Some (Declared_struct, _) =>
          report_error (DeclaredTwiceDifferently C_Struct C_Enum)
      | Some (Declared_union, _) =>
          report_error (DeclaredTwiceDifferently C_Union C_Enum)
      | Some (Defined_struct _, _) =>
          report_error (DefinedDiffFromDeclared C_Struct C_Enum)
      | Some (Defined_union _, _) =>
          report_error (DefinedDiffFromDeclared C_Union C_Enum)
      end
  | CLT_enum (Some s) (Some l) =>
      o <- get_top_SUE_state s;;
      match o with
      | None
      | Some Declared_enum =>
          n <- get_level;;
          record_TypeDecl (CTDecl_enum s);;
          record_TypeDef (CTDef_enum (CTN_named s) (trans_Enumerators l));;
          ret (CT_enum (CTN_named s) n)
      | Some Declared_struct =>
          report_error (DefinedDiffFromDeclared C_Enum C_Struct)
      | Some Declared_union =>
          report_error (DefinedDiffFromDeclared C_Enum C_Union)
      | Some (Defined_struct _) =>
          report_error (DefinedTwice C_Struct C_Enum)
      | Some (Defined_union _) =>
          report_error (DefinedTwice C_Union C_Enum)
      | Some (Defined_enum _) =>
          report_error (DefinedTwice C_Enum C_Enum)
      end
  | CLT_enum None (Some l) =>
      z <- get_and_inc;;
      n <- get_level;;
      record_TypeDef (CTDef_enum (CTN_unnamed z) (trans_Enumerators l));;
      ret (CT_enum (CTN_unnamed z) n)
  end
with trans_RightExpr (t: SimpleCtype) (e: RightExpr): TransM FieldDecl :=
  match e with
  | CRE_annon =>
      z <- get_and_inc;;
      ret {| field_name := CFN_unnamed z; field_type := t |}
  | CRE_var s =>
      ret {| field_name := CFN_named s; field_type := t |}
  | CRE_deref e =>
      trans_RightExpr (CT_pointer t) e
  | CRE_array e olen =>
      trans_RightExpr (CT_array t olen) e
  | CRE_call e args =>
      ts <- foldM (map trans_FT_Argument args);;
      trans_RightExpr (CT_function t ts) e
  end
with trans_FieldsDecl (f: FieldsDecl): TransM (list FieldDecl) :=
  match f with
  | Build_FieldsDecl l r =>
      t <- trans_LeftType l;;
      Fs <- foldM (map (trans_RightExpr t) r);;
      ret Fs
  end
with trans_FT_Argument (arg: FT_Argument): TransM SimpleCtype :=
  match arg with
  | Build_FT_Argument l r =>
      t <- trans_LeftType l;;
      F <- trans_RightExpr t r;;
      ret F.(field_type)
  end.
