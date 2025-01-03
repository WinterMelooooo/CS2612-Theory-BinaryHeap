#include "AsrtUnify.h"

static int poly_type_list_unify(struct PolyTypeListNode * s, struct PolyTypeListNode * t, struct intMapping * exist_mapping);
static int poly_type_unify(struct PolyType * s, struct PolyType * t, struct intMapping * exist_mapping) {
    if (s == NULL && t == NULL) return 1;
    if (s == NULL || t == NULL) return 0;
    switch (s->t) {
    case POLY_VAR: {
        if (intMappingIn(s->d.VAR.id, exist_mapping)) {
            struct mappingValue * mv = intMappingFind(s->d.VAR.id, exist_mapping);
            if (mv->val == NULL) {
                intMappingInsert(s->d.VAR.id, initPolyTypeMappingValue(PolyTypeDeepCopy(t), 1), exist_mapping);
                return 1;
            }
            else {
                return PolyTypeCheckEqual((struct PolyType *)(mv->val), t);
            }
        }
        if (t->t != POLY_VAR) return 0;
        return (s->d.VAR.id == t->d.VAR.id);
    }
    case POLY_FUNCAPP: {
        if (intMappingIn(s->d.FUNCAPP.func, exist_mapping)) {
            struct mappingValue * mv = intMappingFind(s->d.FUNCAPP.func, exist_mapping);
            if (mv->val == NULL) {
                intMappingInsert(s->d.FUNCAPP.func, initPolyTypeMappingValue(PolyTypeDeepCopy(t), 1), exist_mapping);
                return 1;
            }
            else {
                return PolyTypeCheckEqual((struct PolyType *)(mv->val), t);
            }
        }
        if (t->t != POLY_FUNCAPP) return 0;
        if (s->d.FUNCAPP.func != t->d.FUNCAPP.func) return 0;
        return poly_type_list_unify(s->d.FUNCAPP.args->head, t->d.FUNCAPP.args->head, exist_mapping);
    }
    case POLY_ARROW: {
        if (t->t != POLY_ARROW) return 0;
        if (!poly_type_unify(s->d.ARROW.left, t->d.ARROW.left, exist_mapping)) return 0;
        return poly_type_unify(s->d.ARROW.right, t->d.ARROW.right, exist_mapping);
    }
    }
}

static int poly_type_list_unify(struct PolyTypeListNode * s, struct PolyTypeListNode * t, struct intMapping * exist_mapping) {
    if (s == NULL && t == NULL) return 1;
    if (s == NULL || t == NULL) return 0;
    if (!poly_type_unify(s->data, t->data, exist_mapping)) return 0;
    return poly_type_list_unify(s->next, t->next, exist_mapping);
}

static int expr_val_list_unify(struct ExprValListNode * s, struct ExprValListNode * t, struct intMapping * exist_mapping, struct intMapping * local_mapping);
static int expr_val_unify(struct ExprVal * s, struct ExprVal * t, struct intMapping * exist_mapping, struct intMapping * local_mapping) {
    if (s == NULL && t == NULL) return 1;
    if (s == NULL || t == NULL) return 0;
    switch (s->t) {
    case EZ_VAL: {
        if (t->t != EZ_VAL) return 0;
        return s->d.EZ_VAL.number == t->d.EZ_VAL.number;
    }
    case VUOP: {
        if (t->t != VUOP) return 0;
        if (s->d.VUOP.op != t->d.VUOP.op) return 0;
        return expr_val_unify(s->d.VUOP.expr, t->d.VUOP.expr, exist_mapping, local_mapping);
    }
    case VBOP: {
        if (t->t != VBOP) return 0;
        if (s->d.VBOP.op != t->d.VBOP.op) return 0;
        if (!expr_val_unify(s->d.VBOP.expr1, t->d.VBOP.expr1, exist_mapping, local_mapping)) return 0;
        return expr_val_unify(s->d.VBOP.expr2, t->d.VBOP.expr2, exist_mapping, local_mapping);
    }
    case FUNCAPP: {
        if (intMappingIn(s->d.FUNCAPP.id, exist_mapping)) {
            struct mappingValue * mv = intMappingFind(s->d.FUNCAPP.id, exist_mapping);
            if (mv->val == NULL) {
                intMappingInsert(s->d.FUNCAPP.id, initExprValMappingValue(ExprValDeepCopy(t), 1), exist_mapping);
                return 1;
            }
            else {
                return ExprValCheckEqual((struct ExprVal *)(mv->val), t);
            }
        }
        if (intMappingIn(s->d.FUNCAPP.id, local_mapping)) {
            struct ExprVal * expr = (struct ExprVal *) (intMappingFind(s->d.FUNCAPP.id, local_mapping)->val);
            return ExprValCheckEqual(expr, t);
        }
        if (t->t != FUNCAPP) return 0;
        if (s->d.FUNCAPP.id != t->d.FUNCAPP.id) return 0;
        if (!expr_val_list_unify(s->d.FUNCAPP.args->head, t->d.FUNCAPP.args->head, exist_mapping, local_mapping)) return 0;
        return poly_type_list_unify(s->d.FUNCAPP.types->head, t->d.FUNCAPP.types->head, exist_mapping);
    }
    case SIZE_OF: {
        if (t->t != SIZE_OF) return 0;
        return SimpleCtypeCheckEqual(s->d.SIZE_OF.type, t->d.SIZE_OF.type);
    }
    case VFIELD_ADDRESS: {
        if (t->t != VFIELD_ADDRESS) return 0;
        if (s->d.VFIELD_ADDRESS.field_id != t->d.VFIELD_ADDRESS.field_id) return 0;
        return expr_val_unify(s->d.VFIELD_ADDRESS.expr, t->d.VFIELD_ADDRESS.expr, exist_mapping, local_mapping);
    }
    case LINDEX: {
        if (t->t != LINDEX) return 0;
        if (!expr_val_unify(s->d.LINDEX.list, t->d.LINDEX.list, exist_mapping, local_mapping)) return 0;
        return expr_val_unify(s->d.LINDEX.index, t->d.LINDEX.index, exist_mapping, local_mapping);
    }
    case TIME_COST: {
        return t->t == TIME_COST;
    }
    }
}

static int expr_val_list_unify(struct ExprValListNode * s, struct ExprValListNode * t, struct intMapping * exist_mapping, struct intMapping * local_mapping) {
    if (s == NULL && t == NULL) return 1;
    if (s == NULL || t == NULL) return 0;
    if (!expr_val_unify(s->data, t->data, exist_mapping, local_mapping)) return 0;
    return expr_val_list_unify(s->next, t->next, exist_mapping, local_mapping);
}

static int sep_unify(struct Separation * s, struct Separation * t, struct intMapping * exist_mapping, struct intMapping * local_mapping) {
    if (s == NULL && t == NULL) return 1;
    if (s == NULL || t == NULL) return 0;
    if (s->t != t->t) return 0;
    switch (s->t) {
    case T_DATA_AT: {
        if (!expr_val_unify(s->d.DATA_AT.left, t->d.DATA_AT.left, exist_mapping, local_mapping)) return 0;
        if (!SimpleCtypeCheckEqual(s->d.DATA_AT.ty, t->d.DATA_AT.ty)) return 0;
        if (!expr_val_unify(s->d.DATA_AT.right, t->d.DATA_AT.right, exist_mapping, local_mapping)) return 0;
        return 1;
    }
    case T_UNDEF_DATA_AT: {
        if (!expr_val_unify(s->d.UNDEF_DATA_AT.left, t->d.UNDEF_DATA_AT.left, exist_mapping, local_mapping)) return 0;
        if (!SimpleCtypeCheckEqual(s->d.UNDEF_DATA_AT.ty, t->d.UNDEF_DATA_AT.ty)) return 0;
        return 1;
    }
    case T_OTHER: {
        if (s->d.OTHER.sep_id != t->d.OTHER.sep_id) return 0;
        if (!poly_type_list_unify(s->d.OTHER.types->head, t->d.OTHER.types->head, exist_mapping)) return 0;
        if (!expr_val_list_unify(s->d.OTHER.exprs->head, t->d.OTHER.exprs->head, exist_mapping, local_mapping)) return 0;
        return 1;
    }
    case T_ARR: {
        if (!expr_val_unify(s->d.ARR.addr, t->d.ARR.addr, exist_mapping, local_mapping)) return 0;
        if (!SimpleCtypeCheckEqual(s->d.ARR.ty, t->d.ARR.ty)) return 0;
        if (!expr_val_unify(s->d.ARR.value, t->d.ARR.value, exist_mapping, local_mapping)) return 0;
        if (!expr_val_unify(s->d.ARR.size, t->d.ARR.size, exist_mapping, local_mapping)) return 0;
        return 1;
    }
    }
}

static int prop_unify(struct Proposition * s, struct Proposition * t, struct intMapping * exist_mapping, struct intMapping * local_mapping) {
    if (s == NULL && t == NULL) return 1;
    if (s == NULL || t == NULL) return 0;
    if (s->t != t->t) return 0;
    switch (s->t) {
    case T_PROP_PTR: {
        return expr_val_unify(s->d.PTR.expr, t->d.PTR.expr, exist_mapping, local_mapping);
    }
    case T_PROP_UNARY: {
        if (s->d.UNARY.op != t->d.UNARY.op) return 0;
        return prop_unify(s->d.UNARY.prop, t->d.UNARY.prop, exist_mapping, local_mapping);
    }
    case T_PROP_BINARY: {
        if (s->d.BINARY.op != t->d.BINARY.op) return 0;
        if (!prop_unify(s->d.BINARY.prop1, t->d.BINARY.prop1, exist_mapping, local_mapping)) return 0;
        return prop_unify(s->d.BINARY.prop2, t->d.BINARY.prop2, exist_mapping, local_mapping);
    }
    case T_PROP_COMPARE: {
        if (s->d.COMPARE.op != t->d.COMPARE.op) return 0;
        if (!expr_val_unify(s->d.COMPARE.expr1, t->d.COMPARE.expr1, exist_mapping, local_mapping)) return 0;
        return expr_val_unify(s->d.COMPARE.expr2, t->d.COMPARE.expr2, exist_mapping, local_mapping);
    }
    case T_PROP_QUANTIFIER: {
        if (s->d.QUANTIFIER.op != t->d.QUANTIFIER.op) return 0;
        intMappingInsert(s->d.QUANTIFIER.ident, initExprValMappingValue(ExprVal_FUNCAPP(t->d.QUANTIFIER.ident, PolyTypeListNil(), ExprValListNil()), 1), local_mapping);
        return prop_unify(s->d.QUANTIFIER.prop, t->d.QUANTIFIER.prop, exist_mapping, local_mapping);
    }
    case T_PROP_OTHER: {
        if (s->d.OTHER.predicate != t->d.OTHER.predicate) return 0;
        if (!poly_type_list_unify(s->d.OTHER.types->head, t->d.OTHER.types->head, exist_mapping)) return 0;
        if (!expr_val_list_unify(s->d.OTHER.args->head, t->d.OTHER.args->head, exist_mapping, local_mapping)) return 0;
        return 1;
    }
    }
}

struct EntailRetType * asrt_unify(struct Assertion * pre, struct Assertion * post, struct environment * env) {
    struct intMapping * exist_mapping = initIntMapping();
    for (struct ExistList * el = post->exist_list; el != NULL; el = el->next) {
        intMappingInsert(el->id, initExprValMappingValue(NULL, 0), exist_mapping);
    }
    if (exec_info) {
      puts("---------------------------------------------------------------------------------------------");
      printf("Before unification:\n");
      PrintAsrt(pre, env);
      printf("|--\n");
      PrintAsrt(post, env);
    }
    while (1) {
        int flag = 0;
        for (struct SepList * sl_post = post->sep_list; sl_post != NULL;) {
            int _flag = 0;
            struct intMapping * _exist_mapping;
            struct SepList * _sl_pre;
            for (struct SepList * sl_pre = pre->sep_list; sl_pre != NULL; sl_pre = sl_pre->next) {
                struct intMapping * new_exist_mapping = intMappingCopy(exist_mapping);
                struct intMapping * local_mapping = initIntMapping();
                int result = sep_unify(sl_post->head, sl_pre->head, new_exist_mapping, local_mapping);
                finiIntMapping(local_mapping);
                if (result) {
                    if (++_flag == 1) {
                        _exist_mapping = new_exist_mapping;
                        _sl_pre = sl_pre;
                    }
                    else {
                        finiIntMapping(new_exist_mapping);
                    }
                }
                else {
                    finiIntMapping(new_exist_mapping);
                }
            }
            if (_flag == 1) {
                finiIntMapping(exist_mapping);
                exist_mapping = _exist_mapping;
                struct SepList * temp = sl_post->next;
                post->sep_list = SepListRemove(sl_post, post->sep_list);
                pre->sep_list = SepListRemove(_sl_pre, pre->sep_list);
                sl_post = temp;
                flag = 1;
            }
            else {
                sl_post = sl_post->next;
                if (_flag > 1) finiIntMapping(_exist_mapping);
            }
        }
        if (!flag) {
            for (struct PropList * pl_post = post->prop_list; pl_post != NULL;) {
                int _flag = 0;
                struct intMapping * _exist_mapping;
                for (struct PropList * pl_pre = pre->prop_list; pl_pre != NULL; pl_pre = pl_pre->next) {
                    struct intMapping * new_exist_mapping = intMappingCopy(exist_mapping);
                    struct intMapping * local_mapping = initIntMapping();
                    int result = prop_unify(pl_post->head, pl_pre->head, new_exist_mapping, local_mapping);
                    finiIntMapping(local_mapping);
                    if (result) {
                        if (++_flag == 1) {
                            _exist_mapping = new_exist_mapping;
                        }
                        else {
                            finiIntMapping(new_exist_mapping);
                        }
                    }
                    else {
                        finiIntMapping(new_exist_mapping);
                    }
                }
                if (_flag == 1) {
                    finiIntMapping(exist_mapping);
                    exist_mapping = _exist_mapping;
                    struct PropList * temp = pl_post->next;
                    post->prop_list = PropListRemove(pl_post, post->prop_list);
                    pl_post = temp;
                    flag = 1;
                }
                else {
                    pl_post = pl_post->next;
                    if (_flag > 1) finiIntMapping(_exist_mapping);
                }
            }
        }
        if (!flag) break;
    }
    if (exec_info) {
      printf("After unification:\n");
      PrintAsrt(pre, env);
      printf("|--\n");
      PrintAsrt(post, env);
      struct intMappingNode * print_head = exist_mapping->head;
      while (print_head != NULL) {
          printf("%d -> ", print_head->id);
          PrintExprVal(print_head->val->val, env);
          puts("");
          print_head = print_head->next;
      }
      puts("---------------------------------------------------------------------------------------------");
    }
    if (post->sep_list != NULL) {
        finiIntMapping(exist_mapping);
        return NULL;
    }
    struct EntailRetType * ret = CreateEntailRetType(CreateAsrt(), IntListNil(), NULL, NewWitness());
    ret->ex_instance = create_hashtbl(hash_int, int_equal);
    struct intMappingNode * head = exist_mapping->head;
    while (head != NULL) {
        hashtbl_add(ret->ex_instance, (void *)head->id, ExprValDeepCopy(head->val->val));
        head = head->next;
    }
    finiIntMapping(exist_mapping);
    return ret;
}

