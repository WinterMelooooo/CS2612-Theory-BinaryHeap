#include "SimpleCtypeDef.h"

int GetInnerTypeSize(struct SimpleCtype * ty) {
   switch (ty->t) {
      case C_void:
         return 1;
         break;
      case C_int8:
         return 1;
         break;
      case C_int16:
         return 2;
         break;
      case C_int32:
         return 4;
         break;
      case C_int64:
         return 8;
         break;
      case C_pointer:
         return 8;
         break;
      case C_array:
         return GetInnerTypeSize(ty->d.CARRAY.type) * ty->d.CARRAY.length;
         break;
      default:
         fprintf(stderr, "GetInnerTypeSize: not supported %s %d \n", __FILE__, __LINE__);
         exit(-1);
         break;
   }
}

struct SimpleCtype * SimpleCtypeDeepCopy(struct SimpleCtype * ty) {
   if (ty == NULL) return NULL;
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = ty->t;
   switch (ty->t) {
      case C_void:
         break;
      case C_int8:
         res->d.CINT8.s = ty->d.CINT8.s;
         break;
      case C_int16:
         res->d.CINT16.s = ty->d.CINT16.s;
         break;
      case C_int32:
         res->d.CINT32.s = ty->d.CINT32.s;
         break;
      case C_int64:
         res->d.CINT64.s = ty->d.CINT64.s;
         break;
      case C_pointer:
         res->d.CPOINTER.type = SimpleCtypeDeepCopy(ty->d.CPOINTER.type);
         break;
      case C_array:
         res->d.CARRAY.type = SimpleCtypeDeepCopy(ty->d.CARRAY.type);
         res->d.CARRAY.length = ty->d.CARRAY.length;
         break;
      case C_function:
         res->d.CFUNC.ret_type = SimpleCtypeDeepCopy(ty->d.CFUNC.ret_type);
         res->d.CFUNC.arg_list = SimpleCtypeListDeepCopy(ty->d.CFUNC.arg_list);
         break;
      case C_struct:
         res->d.CSTRUCT.struct_id = ty->d.CSTRUCT.struct_id;
         break;
      case C_union:
         res->d.CUNION.union_id = ty->d.CUNION.union_id;
         break;
      case C_enum:
         res->d.CENUM.enum_id = ty->d.CENUM.enum_id;
         break;
   }
   return res;
}

DEFINE_LIST(SimpleCtypeList, struct SimpleCtype*, data)

struct SimpleCtypeListNode* SimpleCtypeListNodeDeepCopy(struct SimpleCtypeListNode * node) {
  if (node == NULL) return NULL;
  struct SimpleCtypeListNode * res = (struct SimpleCtypeListNode *) malloc(sizeof(struct SimpleCtypeListNode));
  res->data = SimpleCtypeDeepCopy(node->data);
  res->next = node->next;
  return res;
}

void SimpleCtypeListNodeFree(struct SimpleCtypeListNode * node) {
  if (node == NULL) return;
  SimpleCtypeFree(node->data);
  free(node);
}

struct SimpleCtype* SimpleCtypeVoid() {
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = C_void;
   return res;
}

struct SimpleCtype* SimpleCtypeInt8(enum Signedness s) {
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = C_int8;
   res->d.CINT8.s = s;
   return res;
}

struct SimpleCtype* SimpleCtypeInt16(enum Signedness s) {
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = C_int16;
   res->d.CINT16.s = s;
   return res;
}

struct SimpleCtype* SimpleCtypeInt32(enum Signedness s) {
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = C_int32;
   res->d.CINT32.s = s;
   return res;
}

struct SimpleCtype* SimpleCtypeInt64(enum Signedness s) {
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = C_int64;
   res->d.CINT64.s = s;
   return res;
}

struct SimpleCtype* SimpleCtypePointer(struct SimpleCtype * type) {
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = C_pointer;
   res->d.CPOINTER.type = type;
   return res;
}

struct SimpleCtype* SimpleCtypeArray(struct SimpleCtype * type, int length) {
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = C_array;
   res->d.CARRAY.type = type;
   res->d.CARRAY.length = length;
   return res;
}

struct SimpleCtype* SimpleCtypeFunction(struct SimpleCtype * ret_type, struct SimpleCtypeList * arg_list) {
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = C_function;
   res->d.CFUNC.ret_type = ret_type;
   res->d.CFUNC.arg_list = arg_list;
   return res;
}

struct SimpleCtype* SimpleCtypeStruct(int struct_id) {
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = C_struct;
   res->d.CSTRUCT.struct_id = struct_id;
   return res;
}

struct SimpleCtype* SimpleCtypeUnion(int union_id) {
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = C_union;
   res->d.CUNION.union_id = union_id;
   return res;
}

struct SimpleCtype* SimpleCtypeEnum(int enum_id) {
   struct SimpleCtype * res = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   res->t = C_enum;
   res->d.CENUM.enum_id = enum_id;
   return res;
}

void SimpleCtypeFree(struct SimpleCtype *ty) {
   if (ty == NULL) return;
   switch (ty->t) {
      case C_void:
      case C_int8:
      case C_int16:
      case C_int32:
      case C_int64:
      case C_struct:
      case C_union:
      case C_enum:
         break;
      case C_pointer:
         SimpleCtypeFree(ty->d.CPOINTER.type);
         break;
      case C_array:
         SimpleCtypeFree(ty->d.CARRAY.type);
         break;
      case C_function:
         SimpleCtypeFree(ty->d.CFUNC.ret_type);
         SimpleCtypeListFree(ty->d.CFUNC.arg_list);
         break;
   }
   free(ty);
}

int SimpleCtypeCheckEqual(struct SimpleCtype * ty1, struct SimpleCtype * ty2) {
   if (ty1 == NULL && ty2 == NULL) return 1;
   if (ty1 == NULL || ty2 == NULL) return 0;
   if (ty1->t != ty2->t) return 0;
   switch (ty1->t) {
      case C_void:
         return 1;
      case C_int8:
         return ty1->d.CINT8.s == ty2->d.CINT8.s;
      case C_int16:
         return ty1->d.CINT16.s == ty2->d.CINT16.s;
      case C_int32:
         return ty1->d.CINT32.s == ty2->d.CINT32.s;
      case C_int64:
         return ty1->d.CINT64.s == ty2->d.CINT64.s;
      case C_pointer:
         return SimpleCtypeCheckEqual(ty1->d.CPOINTER.type, ty2->d.CPOINTER.type);
      case C_array:
         return SimpleCtypeCheckEqual(ty1->d.CARRAY.type, ty2->d.CARRAY.type) && ty1->d.CARRAY.length == ty2->d.CARRAY.length;
      case C_function:
         return SimpleCtypeCheckEqual(ty1->d.CFUNC.ret_type, ty2->d.CFUNC.ret_type) && SimpleCtypeListCheckEqual(ty1->d.CFUNC.arg_list, ty2->d.CFUNC.arg_list);
      case C_struct:
         return ty1->d.CSTRUCT.struct_id == ty2->d.CSTRUCT.struct_id;
      case C_union:
         return ty1->d.CUNION.union_id == ty2->d.CUNION.union_id;
      case C_enum:
         return ty1->d.CENUM.enum_id == ty2->d.CENUM.enum_id;
   }
   return 0;
}

int SimpleCtypeListCheckEqual(struct SimpleCtypeList * list1, struct SimpleCtypeList * list2) {
   if (list1 == NULL && list2 == NULL) return 1;
   if (list1 == NULL || list2 == NULL) return 0;
   struct SimpleCtypeListNode * node1 = list1->head;
   struct SimpleCtypeListNode * node2 = list2->head;
   while (node1 != NULL && node2 != NULL) {
      if (!SimpleCtypeCheckEqual(node1->data, node2->data)) return 0;
      node1 = node1->next;
      node2 = node2->next;
   }
   return node1 == NULL && node2 == NULL;
}

// not equivalent to compatible in C. A pointer to void is acceptable to any pointer type
int SimpleCtypeCheckAcceptable(struct SimpleCtype * ty1, struct SimpleCtype * ty2) {
   if (ty1 == NULL && ty2 == NULL) return 1;
   if (ty1 == NULL || ty2 == NULL) return 0;
   if (ty1->t != ty2->t) return 0;
   switch (ty1->t) {
      case C_void:
         return 1;
      case C_int8:
         return ty1->d.CINT8.s == ty2->d.CINT8.s;
      case C_int16:
         return ty1->d.CINT16.s == ty2->d.CINT16.s;
      case C_int32:
         return ty1->d.CINT32.s == ty2->d.CINT32.s;
      case C_int64:
         return ty1->d.CINT64.s == ty2->d.CINT64.s;
      case C_pointer: {
         if (ty1->d.CPOINTER.type->t == C_void) return 1;
         if (ty2->d.CPOINTER.type->t == C_void) return 1;   
         return SimpleCtypeCheckAcceptable(ty1->d.CPOINTER.type, ty2->d.CPOINTER.type);
      }
      case C_array:
         return SimpleCtypeCheckAcceptable(ty1->d.CARRAY.type, ty2->d.CARRAY.type) && ty1->d.CARRAY.length == ty2->d.CARRAY.length;
      case C_function:
         return SimpleCtypeCheckAcceptable(ty1->d.CFUNC.ret_type, ty2->d.CFUNC.ret_type) && SimpleCtypeListCheckAcceptable(ty1->d.CFUNC.arg_list, ty2->d.CFUNC.arg_list);
      case C_struct:
         return ty1->d.CSTRUCT.struct_id == ty2->d.CSTRUCT.struct_id;
      case C_union:
         return ty1->d.CUNION.union_id == ty2->d.CUNION.union_id;
      case C_enum:
         return ty1->d.CENUM.enum_id == ty2->d.CENUM.enum_id;
   }
   return 0;
}

int SimpleCtypeListCheckAcceptable(struct SimpleCtypeList * list1, struct SimpleCtypeList * list2) {
   if (list1 == NULL && list2 == NULL) return 1;
   if (list1 == NULL || list2 == NULL) return 0;
   struct SimpleCtypeListNode * node1 = list1->head;
   struct SimpleCtypeListNode * node2 = list2->head;
   while (node1 != NULL && node2 != NULL) {
      if (!SimpleCtypeCheckAcceptable(node1->data, node2->data)) return 0;
      node1 = node1->next;
      node2 = node2->next;
   }
   return node1 == NULL && node2 == NULL;
}

int SimpleCtypeIsPointer(struct SimpleCtype * ty) {
   return ty->t == C_pointer;
}

int SimpleCtypeIsIntType(struct SimpleCtype * ty) {
   switch (ty->t) {
      case C_int8:
      case C_int16:
      case C_int32:
      case C_int64:
         return 1;
      default:
         return 0;
   }
}

struct SimpleCtype * GetPointedType(struct SimpleCtype * ty) {
   if (ty->t != C_pointer) {
      fprintf(stderr, "GetPointedType: not a pointer %s %d \n", __FILE__, __LINE__);
      exit(-1);
   }
   return ty->d.CPOINTER.type;
}