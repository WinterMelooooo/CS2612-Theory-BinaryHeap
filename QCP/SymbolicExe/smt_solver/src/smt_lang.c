#include "smt_lang.h"

UFunction* newUFunction(char* name, int numArgs, SmtTerm* t1, SmtTerm* t2, SmtTerm* t3){
    UFunction* res = (UFunction*)malloc(sizeof(UFunction));
    res->name = name;
    res->numArgs = numArgs;
    res->args = malloc(sizeof(SmtTerm*)*numArgs);
    if(numArgs >= 1){
        res->args[0] = t1;
    }
    if(numArgs >= 2){
        res->args[1] = t2;
    }
    if(numArgs == 3){
        res->args[2] = t3;
    }
    return res;
}

SmtTerm* newSmtTerm(int nodetype, int op, int number, char* var, UFunction* uf_term, SmtTerm* t1, SmtTerm* t2){
    SmtTerm* res = (SmtTerm*)malloc(sizeof(SmtTerm));
    memset(res, 0, sizeof(SmtTerm));
    res->type = nodetype;
    switch(nodetype){
        case SMT_LiaBTerm:
            res->term.BTerm.op = op;
            res->term.BTerm.t1 = t1;
            res->term.BTerm.t2 = t2;
            break;
        case SMT_LiaUTerm:
            res->term.UTerm.op = op;
            res->term.UTerm.t = t1;
            break;
        case SMT_NiaBTerm:
            res->term.BTerm.op = op;
            res->term.BTerm.t1 = t1;
            res->term.BTerm.t2 = t2;
            break;
        case SMT_UFTerm:
            res->term.UFTerm = uf_term;
            break;
        case SMT_ConstNum:
            res->term.ConstNum = number;
            break;
        case SMT_VarName:
            res->term.Variable = (char*)malloc(sizeof(char)*(strlen(var)+1));
            memset(res->term.Variable, 0, sizeof(char)*(strlen(var)+1));
            strcpy(res->term.Variable, var);
            break;
        default:
            break;
    }
    return res;
}

SmtProp* newSmtProp(int nodetype, int op, SmtProp* prop1, SmtProp* prop2, SmtTerm* term1, SmtTerm* term2, bool TF){
    SmtProp* res = (SmtProp*)malloc(sizeof(SmtProp));
    memset(res, 0, sizeof(SmtProp));
    res->type = nodetype;
    switch(nodetype){
        case SMTB_PROP:
            res->prop.Binary_prop.op = op;
            res->prop.Binary_prop.prop1 = prop1;
            res->prop.Binary_prop.prop2 = prop2;
            break;
        case SMTU_PROP:
            res->prop.Unary_prop.op = op;
            res->prop.Unary_prop.prop1 = prop1;
            break;
        case SMTAT_PROP_EQ:
        case SMTAT_PROP_LIA:
        case SMTAT_PROP_LIA_EQ:
        case SMTAT_PROP_UF_EQ:
        case SMTAT_PROP_NIA_EQ:
            res->prop.Atomic_prop.op = op;
            res->prop.Atomic_prop.term1 = term1;
            res->prop.Atomic_prop.term2 = term2;
            break;
        case SMTTF_PROP:
            res->prop.TF = TF;
            break;
        case SMT_PROPVAR:
            res->prop.Propvar = op; //复用op来表示命题变元的编号
            break;
        default:
            break;
    }
    return res;
}

void printUFunctionToFile(UFunction* uf, FILE * fp) {
    if(uf->numArgs == 0) fprintf(fp, "%s",uf->name);
    else{
        fprintf(fp, "%s(", uf->name);
        for(int i = 0; i < uf->numArgs - 1; i++){
            printSmtTermToFile(uf->args[i], fp);
            fprintf(fp, ",");
        }
        printSmtTermToFile(uf->args[uf->numArgs-1], fp);
        fprintf(fp, ")");
    }
}

void printUFunction(UFunction* uf){
    printUFunctionToFile(uf, stdout);
}

void printSmtTermToFile(SmtTerm* t, FILE * fp) {
    switch(t->type){
        case SMT_LiaBTerm:
            if(t->term.BTerm.op == LIA_ADD || t->term.BTerm.op == LIA_MINUS){
                fprintf(fp, "(");
                printSmtTermToFile(t->term.BTerm.t1, fp);
                if(t->term.BTerm.op == LIA_ADD) fprintf(fp, " + ");
                else fprintf(fp, " - ");
                printSmtTermToFile(t->term.BTerm.t2, fp);
                fprintf(fp, ")");
            }
            else {
                printSmtTermToFile(t->term.BTerm.t1, fp);
                fprintf(fp, "*");
                printSmtTermToFile(t->term.BTerm.t2, fp);
            }
            break;
        case SMT_NiaBTerm:
            if(t->term.BTerm.op == LIA_MULT || t->term.BTerm.op == LIA_DIV){
                fprintf(fp, "(");
                printSmtTermToFile(t->term.BTerm.t1, fp);
                if(t->term.BTerm.op == LIA_MULT) fprintf(fp, " * ");
                else fprintf(fp, " / ");
                printSmtTermToFile(t->term.BTerm.t2, fp);
                fprintf(fp, ")");
            }
            break;
        case SMT_LiaUTerm:
            if(t->term.UTerm.op == LIA_NEG) fprintf(fp, "(-");
            printSmtTermToFile(t->term.UTerm.t, fp);
            fprintf(fp, ")");
            break;
        case SMT_UFTerm:
            printUFunctionToFile(t->term.UFTerm, fp);
            break;
        case SMT_ConstNum:
            fprintf(fp, "%d",t->term.ConstNum);
            break;
        case SMT_VarNum:
            fprintf(fp, "VAR_%d",t->term.ConstNum);
            break;
        case SMT_VarName:
            fprintf(fp, "%s",t->term.Variable);
            break;
        default:
            fprintf(fp, "error type id : %d\n", t->type);
            fprintf(fp, "invalid type of SmtTerm\n");
            exit(-1);
            break;
    }
}

void printSmtTerm(SmtTerm* t){
    printSmtTermToFile(t, stdout);
}

void printSmtPropToFile(SmtProp* p, FILE * fp) {
    switch(p->type){
        case SMTB_PROP:
            fprintf(fp, "(");
            printSmtPropToFile(p->prop.Binary_prop.prop1, fp);
            switch(p->prop.Binary_prop.op){
                case SMTPROP_AND:
                    fprintf(fp, " /\\ ");
                    break;
                case SMTPROP_OR:
                    fprintf(fp, " \\/ ");
                    break;
                case SMTPROP_IFF:
                    fprintf(fp, " <-> ");
                    break;
                case SMTPROP_IMPLY:
                    fprintf(fp, " -> ");
                    break;
                default: 
                    fprintf(fp, "invalid type of SmtPropBop\n");
                    exit(-1);
                    break;
            }
            printSmtPropToFile(p->prop.Binary_prop.prop2, fp);
            fprintf(fp, ")");
            break;
        case SMTU_PROP:
            fprintf(fp, "(");
            if(p->prop.Unary_prop.op == SMTPROP_NOT)
                fprintf(fp, "NOT ");
            else {
                fprintf(fp, "invalid type of SmtPropUop\n");
                exit(-1);
            }
            printSmtPropToFile(p->prop.Unary_prop.prop1, fp);
            fprintf(fp, ")");
            break;
        case SMTAT_PROP_EQ:
        case SMTAT_PROP_LIA:
        case SMTAT_PROP_UF_EQ:
        case SMTAT_PROP_LIA_EQ:
        case SMTAT_PROP_NIA_EQ:
            printSmtTermToFile(p->prop.Atomic_prop.term1, fp);
            switch(p->prop.Atomic_prop.op){
                case SMT_LE:
                    fprintf(fp, " <= ");
                    break;
                case SMT_LT:
                    fprintf(fp, " < ");
                    break;
                case SMT_GE:
                    fprintf(fp, " >= ");
                    break;
                case SMT_GT:
                    fprintf(fp, " > ");
                    break;
                case SMT_EQ:
                    fprintf(fp, " = ");
                    break;
                default:
                    fprintf(fp, "invalid type of SmtBinPred\n");
                    fprintf(fp, "error id : %d", p->prop.Atomic_prop.op);
                    exit(-1);
                    break;
            }
            printSmtTermToFile(p->prop.Atomic_prop.term2, fp);
            break;
        case SMT_PROPVAR:
            fprintf(fp, "P%d", p->prop.Propvar);
            break;
        case SMTTF_PROP:
            if(p->prop.TF) fprintf(fp, "TT");
            else fprintf(fp, "FF");
            break;
        default:
            fprintf(fp, "invalid type of SmtProp\n");
            exit(-1);
            break;
    }
}

void printSmtProp(SmtProp* p){
    printSmtPropToFile(p, stdout);
}

void printSmtProplistToFile(SmtProplist* p, FILE * fp) {
    SmtProplist* tmp = p;
    while(tmp->next != NULL){
        printSmtPropToFile(tmp->prop, fp);
        fprintf(fp, "\n");
        tmp = tmp->next;
    }
}

void printSmtProplist(SmtProplist* p){
    printSmtProplistToFile(p, stdout);
}

UFunction* copy_UFunction(UFunction* uf){
    UFunction* res = (UFunction*)malloc(sizeof(UFunction));
    res->name = (char*)malloc(sizeof(char)*64);
    memset(res->name, 0, sizeof(char)*64);
    strcpy(res->name, uf->name);
    res->numArgs = uf->numArgs;
    res->args = (SmtTerm**)malloc(sizeof(SmtTerm*)*res->numArgs);
    memset(res->args, 0, sizeof(SmtTerm*)*res->numArgs);
    for(int i = 0; i < res->numArgs; i++){
        res->args[i] = copy_SmtTerm(uf->args[i]);
    }
    return res;
}

SmtTerm* copy_SmtTerm(SmtTerm* t){
    SmtTerm* res = (SmtTerm*)malloc(sizeof(SmtTerm));
    memset(res, 0, sizeof(SmtTerm));
    res->type = t->type;
    switch(t->type){
        case SMT_LiaBTerm:
        case SMT_NiaBTerm:
            res->term.BTerm.t1 = copy_SmtTerm(t->term.BTerm.t1);
            res->term.BTerm.t2 = copy_SmtTerm(t->term.BTerm.t2);
            res->term.BTerm.op = t->term.BTerm.op;
            break;
        case SMT_LiaUTerm:
            res->term.UTerm.t = copy_SmtTerm(t->term.UTerm.t);
            res->term.UTerm.op = t->term.UTerm.op;
            break;
        case SMT_UFTerm:
            res->term.UFTerm = copy_UFunction(t->term.UFTerm);
            break;
        case SMT_ConstNum:
        case SMT_VarNum:
            res->term.ConstNum = t->term.ConstNum;
            break;
        case SMT_VarName:
            res->term.Variable = (char*)malloc(sizeof(char)*64);
            memset(res->term.Variable, 0, sizeof(char)*64);
            strcpy(res->term.Variable, t->term.Variable);
            break;
        default:
            break;
    }
    return res;
} 

SmtProp* copy_SmtProp(SmtProp* p){
    SmtProp* res = (SmtProp*)malloc(sizeof(SmtProp));
    res->type = p->type;
    switch(p->type){
        case SMTB_PROP:
            res->prop.Binary_prop.prop1 = copy_SmtProp(p->prop.Binary_prop.prop1);
            res->prop.Binary_prop.prop2 = copy_SmtProp(p->prop.Binary_prop.prop2);
            res->prop.Binary_prop.op = p->prop.Binary_prop.op;
            break;
        case SMTU_PROP:
            res->prop.Unary_prop.prop1 = copy_SmtProp(p->prop.Unary_prop.prop1);
            res->prop.Unary_prop.op = p->prop.Unary_prop.op;
            break;
        case SMTAT_PROP_EQ:
        case SMTAT_PROP_LIA:
        case SMTAT_PROP_UF_EQ: 
        case SMTAT_PROP_LIA_EQ:
        case SMTAT_PROP_NIA_EQ:
            res->prop.Atomic_prop.term1 = copy_SmtTerm(p->prop.Atomic_prop.term1);
            res->prop.Atomic_prop.term2 = copy_SmtTerm(p->prop.Atomic_prop.term2);
            res->prop.Atomic_prop.op = p->prop.Atomic_prop.op;
            break;
        case SMT_PROPVAR:
            res->prop.Propvar = p->prop.Propvar;
            break;
        case SMTTF_PROP:
            res->prop.TF = p->prop.TF;
            break;
        default:
            break;
    }
    return res;
}

void freeSmtTerm(SmtTerm* t){
    if(t == NULL) return;
    switch(t->type){
        case SMT_LiaBTerm:
            freeSmtTerm(t->term.BTerm.t1);
            freeSmtTerm(t->term.BTerm.t2);
            break;
        case SMT_LiaUTerm:
            freeSmtTerm(t->term.UTerm.t);
            break;
        case SMT_UFTerm:
            for(int i = 0; i < t->term.UFTerm->numArgs; i++){
                freeSmtTerm(t->term.UFTerm->args[i]);
            }
            free(t->term.UFTerm->args);
            free(t->term.UFTerm);
            break;
        case SMT_VarName:
            free(t->term.Variable);
            break;
        case SMT_ConstNum:
        case SMT_VarNum:
        default: break;
    }
    free(t);
}

void freeSmtProp(SmtProp* p){
    if(p == NULL) return;
    switch(p->type){
        case SMTB_PROP:
            freeSmtProp(p->prop.Binary_prop.prop1);
            freeSmtProp(p->prop.Binary_prop.prop2);
            break;
        case SMTU_PROP:
            freeSmtProp(p->prop.Unary_prop.prop1);
            break;
        case SMTAT_PROP_EQ:
        case SMTAT_PROP_LIA:
        case SMTAT_PROP_UF_EQ:
        case SMTAT_PROP_LIA_EQ:
            freeSmtTerm(p->prop.Atomic_prop.term1);
            freeSmtTerm(p->prop.Atomic_prop.term2);
            break;
        case SMT_PROPVAR:
        case SMTTF_PROP:
        default:
            break;
    }
    free(p);
}

void freeSmtProplist(SmtProplist* p){
    if(p == NULL) return;
    freeSmtProp(p->prop);
    SmtProplist* tmp = p->next;
    free(p);
    freeSmtProplist(tmp);
}

bool SmtTerm_eqb(SmtTerm* t1, SmtTerm* t2){
    if(t1 == NULL || t2 == NULL){
        printf("error in SmtTerm_eqb, null pointer\n");
        exit(-1);
    }
    if(t1->type != t2->type) return false;
    switch (t1->type)
    {
    case SMT_LiaBTerm:
    case SMT_NiaBTerm:
        return (t1->term.BTerm.op == t2->term.BTerm.op)
                && (SmtTerm_eqb(t1->term.BTerm.t1, t2->term.BTerm.t1) 
                && SmtTerm_eqb(t1->term.BTerm.t2, t2->term.BTerm.t2));
    case SMT_LiaUTerm:
        return (t1->term.UTerm.op == t2->term.UTerm.op)
                && SmtTerm_eqb(t1->term.UTerm.t, t2->term.UTerm.t);
    case SMT_UFTerm:{
        UFunction* f1 = t1->term.UFTerm;
        UFunction* f2 = t2->term.UFTerm;
        if(f1->numArgs != f2->numArgs || (!strcmp(f1->name, f2->name))) return false;
        for(int i = 0; i < f1->numArgs; i++){
            if(!SmtTerm_eqb(f1->args[i], f2->args[i])) return false;
        }
        return true;
    }
    case SMT_ConstNum:
    case SMT_VarNum:
        return t1->term.ConstNum == t2->term.ConstNum;
    case SMT_VarName:
        if(!strcmp(t1->term.Variable, t2->term.Variable)) return true;
        else return false;
    default:
        printf("error in SmtTerm_eqb, invalid type\n");
        exit(-1);
    }
}

bool SmtProp_eqb(SmtProp* p1, SmtProp* p2){
    if(p1 == NULL || p2 == NULL){
        printf("error in SmtProp_eqb, null pointer\n");
        exit(-1);
    }
    if(p1->type != p2->type) return false;
    switch (p1->type)
    {
    case SMTB_PROP:
        return (p1->prop.Binary_prop.op == p2->prop.Binary_prop.op) 
                && SmtProp_eqb(p1->prop.Binary_prop.prop1, p2->prop.Binary_prop.prop1)
                && SmtProp_eqb(p1->prop.Binary_prop.prop2, p2->prop.Binary_prop.prop2);
    case SMTU_PROP:
        return SmtProp_eqb(p1->prop.Unary_prop.prop1, p2->prop.Unary_prop.prop1);
    case SMTAT_PROP_LIA:
        if(p1->prop.Atomic_prop.op != p2->prop.Atomic_prop.op)
            return false;
    case SMTAT_PROP_EQ:
    case SMTAT_PROP_UF_EQ:
    case SMTAT_PROP_LIA_EQ:
    case SMTAT_PROP_NIA_EQ:
        return SmtTerm_eqb(p1->prop.Atomic_prop.term1, p2->prop.Atomic_prop.term1) 
               && SmtTerm_eqb(p1->prop.Atomic_prop.term2, p2->prop.Atomic_prop.term2);
    case SMT_PROPVAR:
        return p1->prop.Propvar == p2->prop.Propvar;
    case SMTTF_PROP:
        return p1->prop.TF == p2->prop.TF;
    default:
        break;
    }
}

