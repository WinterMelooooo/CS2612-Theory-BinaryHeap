#include <string.h>
#include "TypeTrans.h"
#include "../../compiler/lang.h"
#include "../../compiler/env.h"
#include "../../compiler/hashtbl.h"

struct SimpleCtype * TransBasicType(enum BasicType ty) {
   struct SimpleCtype * ret = (struct SimpleCtype *) malloc(sizeof(struct SimpleCtype));
   switch (ty) {
   case T_VOID:
      ret->t = C_void;
      break;
   case T_CHAR:
      ret->t = C_int8;
      ret->d.CINT8.s = Signed;
      break;
   case T_U8:
      ret->t = C_int8;
      ret->d.CINT8.s = Unsigned;
      break;
   case T_U16:
      ret->t = C_int16;
      ret->d.CINT16.s = Unsigned;
      break;
   case T_SHORT:
      ret->t = C_int16;
      ret->d.CINT32.s = Signed;
      break;
   case T_INT:
      ret->t = C_int32;
      ret->d.CINT32.s = Signed;
      break;
   case T_INT64:
      ret->t = C_int64;
      ret->d.CINT32.s = Signed;
      break;
   case T_UINT:
      ret->t = C_int32;
      ret->d.CINT32.s = Unsigned;
      break;   
   case T_UINT64:
      ret->t = C_int64;
      ret->d.CINT32.s = Unsigned;
      break;      
   default:
      break;
   }
   return ret;
}

struct SimpleCtypeList * TransTypeList(struct type_list *rtype_list) {
   struct SimpleCtypeList * ret = SimpleCtypeListNil();
   for (; rtype_list != NULL; rtype_list = rtype_list->tl)
      ret = SimpleCtypeListSnoc(TransType(rtype_list->hd), ret);
   return ret;
}

struct SimpleCtype * TransType(struct type * rtype) {
   struct SimpleCtype * ret;
   switch (rtype->t) {
      case T_BASIC :
         return TransBasicType(rtype->d.BASIC.ty);
         break;
      case T_STRUCT:
         ret = SimpleCtypeStruct(rtype->d.STRUCT.info->id);
         break;
      case T_UNION:
         ret = SimpleCtypeUnion(rtype->d.UNION.info->id);
         break; 
      case T_ENUM:
         ret = SimpleCtypeInt32(Signed);
         break;
      case T_PTR:
         ret = SimpleCtypePointer(TransType(rtype->d.PTR.ty));
         break;
      case T_ARRAY:
         ret = SimpleCtypeArray(TransType(rtype->d.ARRAY.ty), rtype->d.ARRAY.size);
         break;
      case T_TYPE_ALIAS:
         ret = TransType(rtype->d.TYPE_ALIAS.info->type);
         break;
      case T_FUNCTION:
         ret = SimpleCtypeFunction(TransType(rtype->d.FUNCTION.ret),
                                   TransTypeList(rtype->d.FUNCTION.param));
         break;
      }
   return ret;
}
