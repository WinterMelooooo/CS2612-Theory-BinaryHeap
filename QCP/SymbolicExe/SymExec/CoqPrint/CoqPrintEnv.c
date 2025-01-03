// #include "CoqPrintEnv.h"
// #include "CoqPrintTools.h"
// #include "../Trans/TypeTrans.h"

// void CoqStructDefListPrinter(struct StructDefList * list, FILE * fp) {
//    if (list == NULL) {
//       fprintf(fp, "nil");
//    } else {
//       while (list != NULL) {
//          fprintf(fp, "(");
//          CoqPrintIdent(list->head->name, fp);
//          fprintf(fp, ", ");
//          if (list->head->struct_def == NULL) {
//             fprintf(fp, "nil");
//          } else {
//             fprintf(fp, "(");
//             struct field_dec_list * field;
//             field = list->head->struct_def;
//             while (field != NULL) {
//                fprintf(fp, "(");
//                CoqPrintIdent(field->head->field_name, fp);
//                fprintf(fp, ", ");
//                struct SimpleCtype * simple_ctype;
//                simple_ctype = TransType(field->head->ty);
//                CoqSimpleCtypePrinter(simple_ctype, fp);
//                SimpleCtypeFree(simple_ctype);
//                fprintf(fp, ")");
//                field = field->tail;
//                if (field != NULL) {
//                   fprintf(fp, "::");
//                } else {
//                   fprintf(fp, "::nil)");
//                }
//             }
//          }
//          list = list->next;
//          if (list != NULL) {
//             fprintf(fp, ")::");
//          } else {
//             fprintf(fp, ")::nil");
//          }
//       }
//    }
// }

// void CoqUnionDefListPrinter(struct UnionDefList * list, FILE * fp) {
//    fprintf(fp, "nil");
// }

// void CoqStructPosPrinter(struct StructDefList * list, FILE * fp) {
//    fprintf(fp, "fun start struct_name field_name =>\n");
//    fprintf(fp, "    match struct_name, field_name with\n");
//    while (list != NULL) {
//       struct field_dec_list * field;
//       field = list->head->struct_def;
//       while (field != NULL) {
//          fprintf(fp, "    | ");
//          CoqPrintIdent(list->head->name, fp);
//          fprintf(fp, " ,");
//          CoqPrintIdent(field->head->field_name, fp);
//          fprintf(fp, "  => Integer.Int64.repr (Integer.Int64.unsigned start + %d)\n", field->head->offset);
//          field = field->tail;
//       }
//       list = list->next;
//    }
//    fprintf(fp, "    | _, _ => None\n");
//    fprintf(fp, "    end");
// }

// void CoqUnionPosPrinter(struct UnionDefList * list, FILE * fp) {
//    fprintf(fp, "fun start union_name field_name =>\n");
//    fprintf(fp, "    match union_name, field_name with\n");
//    while (list != NULL) {
//       struct field_dec_list * field;
//       field = list->head->union_def;
//       while (field != NULL) {
//          fprintf(fp, "    | ");
//          CoqPrintIdent(list->head->name, fp);
//          fprintf(fp, " ,");
//          CoqPrintIdent(field->head->field_name, fp);
//          fprintf(fp, "  => (start + %d)\n", field->head->offset);
//          field = field->tail;
//       }
//       list = list->next;
//    }
//    fprintf(fp, "    | _, _ => None\n");
//    fprintf(fp, "    end");
// }

// void CoqStructUnionSizePrinter(struct StructDefList * structs, struct UnionDefList * unions, FILE * fp) {
//    fprintf(fp, "fun name => match name with\n");
//    while (structs != NULL) {
//       fprintf(fp, "| ");
//       CoqPrintIdent(structs->head->name, fp);
//       fprintf(fp, " => %d\n", structs->head->size);
//       structs = structs->next;
//    }
//    while (unions != NULL) {
//       fprintf(fp, "| ");
//       CoqPrintIdent(unions->head->name, fp);
//       fprintf(fp, " => %d\n", unions->head->size);
//       unions = unions->next;
//    }
//    fprintf(fp, "    | _ => 0\n");
//    fprintf(fp, "    end");
// }

// /*
// Record prog_env : Type := {
//   Structdef : list (ident * list (ident * SimpleCtype));
//   Uniondef : list (ident * list (ident * SimpleCtype));
//   struct_pos : int64 -> ident -> ident -> option int64;  (** calculate the position of field of struct *)
//   union_pos : int64 -> ident -> ident -> option int64; (** calculate the position of field of union *)
//   pred_size : ident -> Z;
// }.
// */



// void CoqEnvPrinter(struct Env * env, FILE * fp) {
//    // fprintf(fp, "Definition env :=\n");
//    // fprintf(fp, "{|\n");
//    // fprintf(fp, "  Structure_def :=\n");
//    // fprintf(fp, "  {|\n");
//    // fprintf(fp, "    Structdef := ");
//    // CoqStructDefListPrinter(env->prog_env->struct_def, fp);
//    // fprintf(fp, ";\n");
//    // fprintf(fp, "    Uniondef := ");
//    // CoqUnionDefListPrinter(env->prog_env->union_def, fp);
//    // fprintf(fp, ";\n");
//    // fprintf(fp, "    struct_pos := ");
//    // CoqStructPosPrinter(env->prog_env->struct_def, fp);
//    // fprintf(fp, ";\n");
//    // fprintf(fp, "    union_pos := ");
//    // CoqUnionPosPrinter(env->prog_env->struct_def, fp);
//    // fprintf(fp, ";\n");
//    // fprintf(fp, "    pred_size := ");
//    // CoqStructUnionSizePrinter(env->prog_env->struct_def, env->prog_env->union_def, fp);
//    // fprintf(fp, "\n");
//    // fprintf(fp, "  |};\n");
//    // fprintf(fp, "  Predicate_def :=\n");
//    // fprintf(fp, "  {|\n");
//    // fprintf(fp, "    Funcspecs := nil;\n");
//    // fprintf(fp, "    Funcpreds := nil;\n");
//    // fprintf(fp, "    Seppreds := nil\n");
//    // fprintf(fp, "  |}\n");
//    // fprintf(fp, "|}.\n");
// }


// Definition env :=
// {|
//   Structure_def := 
//   {|
//     Structdef := nil;
//     Uniondef := nil;
//     struct_pos := fun start struct_name field_name =>
//     match struct_name, field_name with
//     | 1%positive, 1%positive => Some start
//     | _, _ => None
//     end;
//     union_pos := fun start union_name field_name =>
//     match union_name, field_name with
//     | 1%positive, 1%positive => Some start
//     | _, _ => None
//     end;
//     pred_size := fun name => match name with
//     | _ => 0
//     end;
//   |};
//   Predicate_def :=
//   {|
//     Funcspecs := nil;
//     Funcpreds := nil;
//     Seppreds := nil
//   |}
// |}.
