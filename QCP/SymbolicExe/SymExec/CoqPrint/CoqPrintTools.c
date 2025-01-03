#include "../../compiler/env.h"
#include "CoqPrintTools.h"
#include "../AsrtDef/SimpleCtypeDef.h"
#include "string.h"

struct CoqAnnot * annot_collector;

struct CoqAnnot *CoqAnnotNil() { return NULL; }

struct CoqAnnot *CoqAnnotCons(char *name, int id, int is_var, struct CoqAnnot *list) {
   struct CoqAnnot * ret = (struct CoqAnnot *) malloc(sizeof(struct CoqAnnot));
   ret->name = (char *) malloc(sizeof(char) * (strlen(name) + 1));
   strcpy(ret->name, name);
   ret->id = id;
   ret->next = list;
   ret->is_var = is_var;
   return ret;
}

struct CoqAnnot *CoqAnnotFind(char *name, struct CoqAnnot *list) {
   while (list != NULL) {
      if (strcmp(name, list->name) == 0) {
         return list;
      }
      list = list->next;
   }
   return NULL;
}

// 1: new, 0: old, -1: conflict
int CoqCollectAnnots(char *name, int id, int is_var) {
   struct CoqAnnot * i = CoqAnnotFind(name, annot_collector);
   if (i == NULL) {
      annot_collector = CoqAnnotCons(name, id, is_var, annot_collector);
      return 1;
   } else if (i->id != id) {
      return -1;
   }
   return 0;
}

void CoqPrintCollectedAnnots(struct environment * env, FILE * fp) {
   struct CoqAnnot * i = annot_collector;
   while (i != NULL) {
      if (i->id == -1) {
         fprintf(stderr, "Error: CoqPrintCollectedAnnots: %s %d\n", __FILE__, __LINE__);
         exit(1);
      } else {
         if (i->is_var == 1) {
            fprintf(fp, "Definition %s := (%d%%positive, 0%%nat).\n", i->name, i->id);
         } else if (i->is_var == 0) {
            fprintf(fp, "Definition %s := %d%%positive.\n", i->name, i->id);
         } else if (i->is_var == 2) {
            fprintf(fp, "Definition %s := V_vari %d%%positive.\n", i->name, i->id);
         }
      }
      i = i->next;
   }
   int max_id = env->persist.next_fresh;
   for (int i = 1; i <= max_id; ++i) {
      fprintf(fp, "Definition _%d := %d%%positive.\n", i, i);
   }
   fprintf(fp, "\n");
}

int CoqPrintRawAnnots(char *name, int id, int is_var, FILE *fp) {
   if (strcmp(name, "nil") == 0) name = "NIL";
   CoqCollectAnnots(name, id, is_var);
   fprintf(fp, "%s", name);
   return 0;
}

void CoqPrintVarName(char *name, int id, FILE * fp) {
   char *name_with_id;
   int len = 0;
   if (id == 0) {
      len = 1;
   } else {
      int tmp = id;
      while (tmp > 0) {
         tmp /= 10;
         len++;
      }
   }
   name_with_id = (char *) malloc(sizeof(char) * (strlen(name) + len + 2));
   sprintf(name_with_id, "%s_%d", name, id);
   fprintf(fp, "%s", name_with_id);
   CoqCollectAnnots(name_with_id, id, 1);
   free(name_with_id);
}

void CoqPrintIdent(int id, FILE * fp) {
   fprintf(fp, "_%d", id);
}

void CoqSignednessPrinter(enum Signedness s, FILE * fp) {
   switch (s) {
      case Signed:
         fprintf(fp, "Signed");
         break;
      case Unsigned:
         fprintf(fp, "Unsigned");
         break;
      default: {
         fprintf(stderr, "Error: PrintSignedness: unknown signedness %s %d\n", __FILE__, __LINE__);
         exit(1);
         break;
      }
   }
}

void CoqSimpleCtypePrinter(struct SimpleCtype * type, struct environment * env, FILE * fp) {
   fprintf(fp, "(");
   switch (type->t) {
      case C_void:
         fprintf(fp, "C_void");
         break;
      case C_int8:
         fprintf(fp, "C_int8 ");
         CoqSignednessPrinter(type->d.CINT8.s, fp);
         break;
      case C_int16:
         fprintf(fp, "C_int16 ");
         CoqSignednessPrinter(type->d.CINT16.s, fp);
         break;
      case C_int32:
         fprintf(fp, "C_int32 ");
         CoqSignednessPrinter(type->d.CINT32.s, fp);
         break;
      case C_int64:
         fprintf(fp, "C_int64 ");
         CoqSignednessPrinter(type->d.CINT64.s, fp);
         break;
      case C_pointer:
         fprintf(fp, "C_pointer ");
         CoqSimpleCtypePrinter(type->d.CPOINTER.type, env, fp);
         break;
      case C_array:
         fprintf(fp, "C_array ");
         CoqSimpleCtypePrinter(type->d.CARRAY.type, env, fp);
         fprintf(fp, " %d", type->d.CARRAY.length);
         break;
      case C_function: {
         fprintf(fp, "C_function ");
         CoqSimpleCtypePrinter(type->d.CFUNC.ret_type, env, fp);
         fprintf(fp, " ");
         struct SimpleCtypeListNode * tmp;
         tmp = type->d.CFUNC.arg_list->head;
         while (tmp != NULL) {
            CoqSimpleCtypePrinter(tmp->data, env, fp);
            fprintf(fp, " ");
            tmp = tmp->next;
         }
         break;
      }
      case C_struct: {
         fprintf(fp, "C_struct ");
         struct struct_union_info * info = find_struct_by_id(type->d.CSTRUCT.struct_id, &env->persist);
         CoqPrintRawAnnots(info->name, info->id, 0, fp);
         break;
      }
      case C_union:
         fprintf(fp, "C_union ");
         struct struct_union_info * info = find_union_by_id(type->d.CUNION.union_id, &env->persist);
         CoqPrintRawAnnots(info->name, info->id, 0, fp);
         break;
      case C_enum:
         fprintf(fp, "C_enum ");
         struct enum_info * enum_info = find_enum_by_id(type->d.CENUM.enum_id, &env->persist);
         CoqPrintRawAnnots(enum_info->name, enum_info->id, 0, fp);
         break;
      default:
         break;
   }
   fprintf(fp, ")");
}
