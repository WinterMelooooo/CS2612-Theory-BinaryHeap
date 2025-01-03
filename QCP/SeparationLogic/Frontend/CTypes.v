Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import SimpleC.Common.CTypes.

Record Enumerator: Type :=
  {
    enumerator_name: string;
    enumerator_value: option Z;
  }.

Inductive LeftType: Type :=
  | CLT_basic (t: CBasicType): LeftType
    (** basic types like integers and void *)
  | CLT_alias (t: string): LeftType
  | CLT_struct
      (i: option string)
      (m: option (list FieldsDecl)): LeftType
    (** CLT_struct (Some s) (Some [f1; f2; ...; fn]) defines
          a new struct: struct s {f1; f2; ...; fn; };
        CLT_struct None (Some [f1; f2; ...; fn]) defines
          an anonymous struct: struct {f1; f2; ...; fn; };
        CLT_struct (Some s) None declares the existence of
          struct s. *)
  | CLT_union
      (i: option string)
      (m: option (list FieldsDecl)): LeftType
    (** CLT_union (Some s) (Some [f1; f2; ...; fn]) defines
          a new union: union s {f1; f2; ...; fn; };
        CLT_union None (Some [f1; f2; ...; fn]) defines
          an anonymous union: union {f1; f2; ...; fn; };
        CLT_union (Some s) None declares the existence of
          union s. *)
  | CLT_enum
      (i: option string)
      (es: option (list Enumerator)): LeftType
    (** CLT_enum (Some s) (Some [e1; e2; ...; en]) defines
          a new enum type: enum s {e1, e2, ..., en };
        CLT_enum None (Some [e1; e2; ...; en]) defines
          an anonymous enum type: enum {e1, e2, ..., en };
        CLT_enum (Some s) None declares the existence of
          enum s. *)
with RightExpr: Type :=
  | CRE_annon: RightExpr
  | CRE_var (i: string): RightExpr
  | CRE_deref (e: RightExpr): RightExpr
  | CRE_array (e: RightExpr) (len: option Z): RightExpr
    (** CRE_array x (Some n) defines x[n];
        CRE_array x None defines x[] *)
  | CRE_call (e: RightExpr) (args: list FT_Argument): RightExpr
with FieldsDecl: Type :=
  | Build_FieldsDecl (l: LeftType) (r: list RightExpr): FieldsDecl
    (** multiple fields may be defined by one LeftType,
        a field can be unnamed *)
with FT_Argument: Type :=
  | Build_FT_Argument
      (l: LeftType) (r: RightExpr): FT_Argument.

(** Impossible: struct 不能既没有名字有没有field
    Error: 不定长数组不能是数组的基类型，等其他限制，不能是struct的field（最后一个field除外），不能是union的field，不定长数组的指针？？函数返回值是数组？不定长数组？匿名struct/union域造成的域名冲突。不开-fms-extensions时，匿名域必须是一个匿名struct/union，开-fms-extensions时，匿名域可以是其他方式定义的struct/union，但是依然不能是别的类型。
    Unsupported：不定长数组不能是struct的最后一个field。 -fplan9-extensions对于unnamed fields的其他许可条件。
    *)

(** TODO 数组长度允许用表达式 *)

Inductive TypeDefDecl: Type :=
  | CTD_struct
      (i: string) (m: option (list FieldsDecl)): TypeDefDecl
  | CTD_union
      (i: string) (m: option (list FieldsDecl)): TypeDefDecl
  | CTD_enum
      (i: string) (es: option (list Enumerator)): TypeDefDecl
  | CTD_alias
      (t: LeftType) (e: RightExpr): TypeDefDecl.

(** Impossible: typedef has an unnamed RightExpr *)


