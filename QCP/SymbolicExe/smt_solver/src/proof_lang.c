#include "proof_lang.h"
#define MAX_CONCL_NUM 20

ProofTerm *newProofTerm(TermType type, char *name, int number, ProofTerm *arg1, ProofTerm *arg2)
{
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->type = type;
    switch (type)
    {
    case FUNC_NOT:
    {
        res->arg_num = 1;
        res->args = (ProofTerm **)malloc(sizeof(ProofTerm *));
        memset(res->args, 0, sizeof(ProofTerm *));
        res->args[0] = arg1;
        break;
    }
    case FUNC_EQ:
    {
        res->arg_num = 2;
        res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * 2);
        memset(res->args, 0, sizeof(ProofTerm *) * 2);
        res->args[0] = arg1;
        res->args[1] = arg2;
        break;
    }
    case PROP_VAR:
    case VAR:
    {
        res->arg_num = 0;
        res->func_name.node_number = number;
        break;
    }
    case INT_CONST:
    {
        res->arg_num = 0;
        res->func_name.const_val = number;
        break;
    }
    case PROOFNODE_CONCL:
    {
        res->arg_num = 0;
        res->func_name.node_number = number;
        break;
    }
    case PROP_FALSE:
    {
        res->arg_num = 0;
        break;
    }
    default:
    {
        printf("invalid type in newProofTerm\n");
        exit(-1);
    }
    }
    return res;
}

ProofTerm *newFalseTerm()
{
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->type = PROP_FALSE;
    return res;
}

ProofNode *newProofNode(int *plist, int node_number, ProofRule rule, ProofTerm *concl, ArgTerm *arg, int premise_num)
{
    ProofNode *res = (ProofNode *)malloc(sizeof(ProofNode));
    memset(res, 0, sizeof(ProofNode));
    res->node_number = node_number;
    res->premise_num = premise_num;
    res->rule = rule;
    res->concl = concl;
    res->premise_list = plist;
    switch (rule)
    {
    case ASSUME:
    {
        res->premise_num = 0;
        res->arg_num = 1;
        res->args = (ArgTerm **)malloc(sizeof(ArgTerm *));
        res->args[0] = arg;
        break;
    }
    case SCOPE:
    {
        res->arg_num = 1;
        res->args = (ArgTerm **)malloc(sizeof(ArgTerm *));
        res->args[0] = arg;
        break;
    }
    case SET_VAR:
    {
        res->arg_num = 1;
        res->args = (ArgTerm **)malloc(sizeof(ArgTerm *));
        res->args[0] = arg;
        break;
    }
    case SET_PROP_IFF:
    case SET_PROP:
    {
        res->arg_num = 1;
        res->args = (ArgTerm **)malloc(sizeof(ArgTerm *));
        res->args[0] = arg;
        break;
    }
    case CNF_TRANS:
    case SUB_VAR:
    case SUB_PROP:
    case SUB_PROP_IFF:
    case NOT_AND:
    case NOT_ELIM:
    {
        res->arg_num = 0;
        res->args = NULL;
        break;
    }
    case RESOLUTION:
    case AND_ELIM:
    {
        res->arg_num = 1;
        res->args = (ArgTerm **)malloc(sizeof(ArgTerm *));
        res->args[0] = arg;
        break;
    }
    case EQUALITY_RESOLUTION:
    case FUNC_REWRITE:
    {
        res->arg_num = 0;
        res->args = NULL;
        break;
    }
    case ARITH_EQ_ELIM:
    case ARITH_FME:
    {
        res->premise_num = 2;
        res->arg_num = 1;
        res->args = (ArgTerm **)malloc(sizeof(ArgTerm *));
        res->args[0] = arg;
        break;
    }
    case ARITH_FALSE:
    {
        res->premise_num = 1;
        res->arg_num = 0;
        break;
    }
    case REFL:
    case CONG:
    {
        res->arg_num = 1;
        res->args = (ArgTerm **)malloc(sizeof(ArgTerm *));
        res->args[0] = arg;
        break;
    }
    case SYMM:
    case TRANS:
    case ARITH_NOT_ELIM:
    case ARITH_EQ_INTRO:
    case ARITH_TRANS:
    case UF_CONTRA_FALSE:
    case LIA_TRANS:
    {
        res->arg_num = 0;
        res->args = NULL;
        break;
    }
    default:
    {
        printf("invalid arg in newProofNode: %d\n", rule);
        exit(-1);
    }
    }
    return res;
}

char *ProofTerm2str(ProofTerm *t)
{
    switch (t->type)
    {
    case FUNC_AND:
    case FUNC_OR:
    case FUNC_IMPLY:
    case FUNC_IFF:
    case FUNC_NOT:
    case FUNC_EQ:
    case FUNC_LE:
    case FUNC_LT:
    case FUNC_GE:
    case FUNC_GT:
    case FUNC_EQ0:
    case FUNC_LE0:
    case FUNC_ADD:
    case FUNC_MINUS:
    case FUNC_MULT:
    case FUNC_DIV:
    case FUNC_NEG:
    {
        char **arg = (char **)malloc(sizeof(char *) * (t->arg_num));
        memset(arg, 0, sizeof(char *) * (t->arg_num));
        int len = 7; //"func%d(",%d可能为两位数
        for (int i = 0; i < t->arg_num; i++)
        {
            arg[i] = ProofTerm2str(t->args[i]);
            len += strlen(arg[i]) + 1;
        }
        char *res = (char *)malloc(sizeof(char) * (len + 1));
        memset(res, 0, sizeof(char) * (len + 1));
        sprintf(res, "func%d(", t->type);
        for (int i = 0; i < t->arg_num; ++i)
        {
            strcat(res, arg[i]);
            free(arg[i]);
            if (i < t->arg_num - 1)
            {
                strcat(res, ",");
            }
        }
        strcat(res, ")");
        free(arg);
        return res;
    }
    case PROP_VAR:
    {
        char *res = (char *)malloc(sizeof(char) * 8);
        sprintf(res, "PROP_%d", t->func_name.node_number);
        return res;
    }
    case VAR:
    {
        char *res = (char *)malloc(sizeof(char) * 8);
        sprintf(res, "VAR_%d", t->func_name.node_number);
        return res;
    }
    case INT_CONST:
    {
        char *res = (char *)malloc(sizeof(char) * 16);
        sprintf(res, "%d", t->func_name.const_val);
        return res;
    }
    case FUNC_N:
    {
        char **arg = (char **)malloc(sizeof(char *) * (t->arg_num));
        memset(arg, 0, sizeof(char *) * (t->arg_num));
        int len = strlen(t->func_name.name) + 2; 
        for (int i = 0; i < t->arg_num; i++)
        {
            arg[i] = ProofTerm2str(t->args[i]);
            len += strlen(arg[i]) + 1;
        }
        char *res = (char *)malloc(sizeof(char) * (len + 1));
        memset(res, 0, sizeof(char) * (len + 1));
        sprintf(res, "%s(", t->func_name.name);
        for (int i = 0; i < t->arg_num; ++i)
        {
            strcat(res, arg[i]);
            free(arg[i]);
            if (i < t->arg_num - 1)
            {
                strcat(res, ",");
            }
        }
        strcat(res, ")");
        return res;
    }
    case PROOFNODE_CONCL:
    {
        char *res = (char *)malloc(sizeof(char) * 8);
        sprintf(res, "@p%d", t->func_name.node_number);
        return res;
    }
    case PROP_FALSE:
    {
        char *res = strdup("False");
        return res;
    }
    case PROP_TRUE:
    {
        char *res = strdup("True");
        return res;
    }
    default:
        printf("error in ProofTerm2str, invalide TermType %d\n", t->type);
        exit(-1);
    }
    return NULL;
}

void freeProofTerm(ProofTerm *t)
{
    if (t == NULL)
        return;
    for (int i = 0; i < t->arg_num; i++)
    {
        freeProofTerm(t->args[i]);
        t->args[i] = NULL;
    }
    if (t->args != NULL)
        free(t->args);
    t->args = NULL;
    if (t->type == FUNC_N)
    {
        free(t->func_name.name);
        t->func_name.name = NULL;
    }
    free(t);
}

void freeProofNode(ProofNode *node)
{
    if (node == NULL)
        return;
    freeProofTerm(node->concl);
    node->concl = NULL;
    free(node->premise_list);
    node->premise_list = NULL;
    for (int i = 0; i < node->arg_num; i++)
    {
        if (node->args[i]->type == N_FUNC)
        {
            free(node->args[i]->args.func_name);
            node->args[i]->args.func_name = NULL;
        }
        else if (node->args[i]->type == PTERM)
        {
            freeProofTerm(node->args[i]->args.pterm);
            node->args[i]->args.pterm = NULL;
        }
        free(node->args[i]);
        node->args[i] = NULL;
    }
    free(node->args);
    node->args = NULL;
    free(node);
}

ProofTerm *copy_ProofTerm(const ProofTerm *t)
{
    if (t == NULL)
        return NULL;
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->type = t->type;
    res->arg_num = t->arg_num;
    if (res->type == FUNC_N)
    {
        res->func_name.name = strdup(t->func_name.name);
    }
    else if (res->type == INT_CONST)
    {
        res->func_name.const_val = t->func_name.const_val;
    }
    else
    {
        res->func_name.node_number = t->func_name.node_number;
    }
    res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * (res->arg_num));
    memset(res->args, 0, sizeof(ProofTerm *) * (res->arg_num));
    for (int i = 0; i < res->arg_num; i++)
    {
        res->args[i] = copy_ProofTerm(t->args[i]);
    }
    return res;
}

// just for test
ProofData *initProofData()
{
    ProofData *pdata = (ProofData *)malloc(sizeof(ProofData));
    memset(pdata, 0, sizeof(ProofData));
    pdata->cur_num = 0;
    pdata->max_num = MAX_CONCL_NUM;
    pdata->declare_num = 0;
    pdata->declare_max_num = MAX_CONCL_NUM;
    pdata->local_table = creat_hash_table();
    pdata->theory_global_table = creat_hash_table();
    pdata->global_table = creat_hash_table();
    pdata->node_table = (ProofNode **)malloc(sizeof(ProofNode *) * (MAX_CONCL_NUM + 1));
    memset(pdata->node_table, 0, sizeof(ProofNode *) * (MAX_CONCL_NUM + 1));
    pdata->declare_table = (ProofNode **)malloc(sizeof(ProofNode *) * (MAX_CONCL_NUM + 1));
    memset(pdata->declare_table, 0, sizeof(ProofNode *) * (MAX_CONCL_NUM + 1));
    return pdata;
}

void printProofTerm(ProofTerm *t)
{
    if (t == NULL)
        return;
    switch (t->type)
    {
    case FUNC_EQ0:
    case FUNC_LE0:
    {
        for (int i = 1; i <= t->arg_num - 1; i++)
        {
            printf("%d*v%d + ", t->args[i]->func_name.const_val, i);
        }
        if (t->type == FUNC_EQ0)
            printf("%d = 0 ", t->args[0]->func_name.const_val);
        else if (t->type == FUNC_LE0)
            printf("%d <= 0 ", t->args[0]->func_name.const_val);
        break;
    }
    case VAR:
    {
        printf("v%d", t->func_name.node_number);
        break;
    }
    case PROP_VAR:
    {
        printf("P%d", t->func_name.node_number);
        break;
    }
    case INT_CONST:
    {
        printf("%d", t->func_name.const_val);
        break;
    }
    case FUNC_AND:
    {
        printf("(");
        for (int i = 0; i < t->arg_num - 1; i++)
        {
            printProofTerm(t->args[i]);
            printf(" /\\ ");
        }
        printProofTerm(t->args[t->arg_num - 1]);
        printf(")");
        break;
    }
    case FUNC_OR:
    {
        printf("(");
        for (int i = 0; i < t->arg_num - 1; i++)
        {
            printProofTerm(t->args[i]);
            printf(" \\/ ");
        }
        printProofTerm(t->args[t->arg_num - 1]);
        printf(")");
        break;
    }
    case FUNC_IMPLY:
    {
        printf("(");
        printProofTerm(t->args[0]);
        printf(" -> ");
        printProofTerm(t->args[1]);
        printf(")");
        break;
    }
    case FUNC_IFF:
    {
        printf("(");
        printProofTerm(t->args[0]);
        printf(" <-> ");
        printProofTerm(t->args[1]);
        printf(")");
        break;
    }
    case FUNC_LE:
    {
        printf("(");
        printProofTerm(t->args[0]);
        printf(" <= ");
        printProofTerm(t->args[1]);
        printf(")");
        break;
    }
    case FUNC_LT:
    {
        printf("(");
        printProofTerm(t->args[0]);
        printf(" < ");
        printProofTerm(t->args[1]);
        printf(")");
        break;
    }
    case FUNC_GE:
    {
        printf("(");
        printProofTerm(t->args[0]);
        printf(" >= ");
        printProofTerm(t->args[1]);
        printf(")");
        break;
    }
    case FUNC_GT:
    {
        printf("(");
        printProofTerm(t->args[0]);
        printf(" > ");
        printProofTerm(t->args[1]);
        printf(")");
        break;
    }
    case FUNC_EQ:
    {
        printf("(");
        printProofTerm(t->args[0]);
        printf(" = ");
        printProofTerm(t->args[1]);
        printf(")");
        break;
    }
    case FUNC_ADD:
    {
        printf("(");
        printProofTerm(t->args[0]);
        printf(" + ");
        printProofTerm(t->args[1]);
        printf(")");
        break;
    }
    case FUNC_MINUS:
    {
        printf("(");
        printProofTerm(t->args[0]);
        printf(" - ");
        printProofTerm(t->args[1]);
        printf(")");
        break;
    }
    case FUNC_MULT:
    {
        printf("(");
        printProofTerm(t->args[0]);
        printf(" * ");
        printProofTerm(t->args[1]);
        printf(")");
        break;
    }
    case FUNC_DIV:
    {
        printf("(");
        printProofTerm(t->args[0]);
        printf(" / ");
        printProofTerm(t->args[1]);
        printf(")");
        break;
    }
    case FUNC_NEG:
    {
        printf("(");
        printf(" - ");
        printProofTerm(t->args[0]);
        printf(")");
        break;
    }
    case FUNC_N:
    {
        printf("%s(", t->func_name.name);
        for (int i = 0; i < t->arg_num - 1; i++)
        {
            printProofTerm(t->args[i]);
            printf(",");
        }
        printProofTerm(t->args[t->arg_num - 1]);
        printf(")");
        break;
    }
    case FUNC_NOT:
    {
        printf("NOT (");
        printProofTerm(t->args[0]);
        printf(")");
        break;
    }
    case PROP_FALSE:
    {
        printf("FALSE");
        break;
    }
    case PROP_TRUE:
    {
        printf("TRUE");
        break;
    }
    default:
        break;
    }
}

void printProofTerm_prefix(ProofTerm* t, FILE* fp){
    if(t == NULL) return;
    switch(t->type){
        case FUNC_AND:{
            fprintf(fp, "SMT_AND:%d:", t->arg_num);
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_OR:{
            fprintf(fp, "SMT_OR:%d:", t->arg_num);
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_IMPLY:{
            fprintf(fp, "SMT_IMPLY:");
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_IFF:{
            fprintf(fp, "SMT_IFF:");
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_NOT:{
            fprintf(fp, "SMT_NOT:");
            fprintf(fp,"(");
            printProofTerm_prefix(t->args[0], fp);
            fprintf(fp,")");
            break;
        }
        case FUNC_EQ:{
            fprintf(fp, "SMT_EQ:");
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_LE:{
            fprintf(fp, "SMT_LE:");
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_LT:{
            fprintf(fp, "SMT_LT:");
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_GE:{
            fprintf(fp, "SMT_GE:");
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_GT:{
            fprintf(fp, "SMT_GT:");
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_LE0:{
            fprintf(fp, "SMT_LE0:%d:", t->arg_num);
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp, "(");
                fprintf(fp, "%d", t->args[i]->func_name.const_val);
                fprintf(fp, ")");
            }
            break;
        }
        case FUNC_EQ0:{
            fprintf(fp, "SMT_EQ0:%d:", t->arg_num);
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp, "(");
                fprintf(fp, "%d", t->args[i]->func_name.const_val);
                fprintf(fp, ")");
            }
            break;
        }
        case PROP_VAR:{
            fprintf(fp, "SMT_PVAR:%d", t->func_name.node_number);
            break;
        }
        case FUNC_ADD:{
            fprintf(fp, "SMT_ADD:");
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_MINUS:{
            fprintf(fp, "SMT_MINUS:");
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_MULT:{
            fprintf(fp, "SMT_MULT:");
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_DIV:{
            fprintf(fp, "SMT_DIV:");
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case FUNC_NEG:{
            fprintf(fp, "SMT_NEG:");
            printProofTerm_prefix(t->args[0], fp);
            break;
        }
        case VAR:{
            fprintf(fp, "SMT_VAR:%d", t->func_name.node_number);
            break;
        }
        case INT_CONST:{
            fprintf(fp, "SMT_NUM:%d", t->func_name.const_val);
            break;
        }
        case FUNC_N:{
            fprintf(fp, "SMT_FUNCN:%s:%d", t->func_name.name, t->arg_num);
            for(int i = 0; i < t->arg_num; i++){
                fprintf(fp,"(");
                printProofTerm_prefix(t->args[i], fp);
                fprintf(fp,")");
            }
            break;
        }
        case PROOFNODE_CONCL:{
            fprintf(fp, "@p%d", t->func_name.node_number);
            break;
        }
        case PROP_FALSE:{
            fprintf(fp, "FF");
            break;
        }
        case PROP_TRUE:{
            fprintf(fp, "TT");
            break;
        }
        default:{
            printf("unexpected type in printProofTerm_prefix\n");
            break;
        }
    }
    return;
}

void printArgTerm(ArgTerm* t, ProofRule rule, FILE* fp){
    switch (rule){
        case ASSUME:{
            printProofTerm_prefix(t->args.pterm, fp);
            break;
        }
        case SCOPE:{
            fprintf(fp, "@p%d", t->args.number);
            break;
        }
        case SET_VAR:
        case SET_PROP:
        case SET_PROP_IFF:{
            printProofTerm_prefix(t->args.pterm, fp);
            break;
        }
        case SUB_VAR:
        case SUB_PROP:
        case SUB_PROP_IFF:
        case CNF_TRANS:{
            fprintf(fp, "@p%d", t->args.number);
            break;
        }
        case RESOLUTION:
        case AND_ELIM:
        case ARITH_FME:
        case ARITH_EQ_ELIM:{
            fprintf(fp,"%d", t->args.number);
            break;
        }
        case ARITH_EQ_INTRO:{
            fprintf(fp,"%d", t->args.number);
            break;
        }
        case CONG:{
            fprintf(fp,"%s",t->args.func_name);
            break;
        }
        default:{
            printf("error in printArgTerm, should not step in this fun, rule%d\n", rule);
        }
    }
}

void printProofNode_formal(ProofNode* node, FILE* fp){
    if(node == NULL) return;
    if(node->rule == DECLARE){
        fprintf(fp, "step@p0:\n");
        fprintf(fp, "rule:DECLARE\n");
        fprintf(fp,"premise:0:()\n");
        if(node->arg_num == 2){
            fprintf(fp, "args:2:(%d)(%s)\n", node->args[0]->args.number, node->args[1]->args.func_name);
        }
        else {
            fprintf(fp, "args:1:(%s)\n", node->args[0]->args.func_name);
        }
        fprintf(fp,"concl:()\n");
        return;
    }
    fprintf(fp, "step@p%d:\n",node->node_number);
    fprintf(fp, "rule:%d\n", node->rule);
    fprintf(fp, "premise:%d:", node->premise_num);
    for(int i = 0; i < node->premise_num; i++){
        fprintf(fp, "(@p%d)", node->premise_list[i]);
    }
    fprintf(fp, "\narg:%d:", node->arg_num);
    for(int i = 0; i < node->arg_num; i++){
        fprintf(fp,"(");
        printArgTerm(node->args[i], node->rule, fp);
        fprintf(fp, ")");
    }
    fprintf(fp,"\nconcl:(");
    printProofTerm_prefix(node->concl, fp);
    fprintf(fp,")\n");
}

void printSmtProof(SMT_PROOF* proof, FILE* fp){
    fprintf(fp, "Proof Start:\n");
    for(int i = 1; i <= proof->declare_num; i++) printProofNode_formal(proof->declare_table[i], fp);
    for(int i = 1; i <= proof->proof_num; i++) printProofNode_formal(proof->proof_table[i], fp);
    fprintf(fp, "Proof End\n");
}

void printProofNode(ProofData *data, ProofNode *node)
{   
    
    if (node == NULL) return;
    if(node->rule == DECLARE){
        if(node->arg_num == 2){
            printf("declare-var: v%d = %s\n", node->args[0]->args.number, node->args[1]->args.func_name);
        }
        else if(node->arg_num == 1){
            printf("declare-fun: %s\n", node->args[0]->args.func_name);
        }
        return;
    }
    printf("step@p%d ", node->node_number);
    switch (node->rule)
    {
    case ASSUME:
    {
        printf(":rule ASSUME\n");
        printf("premise ()\n");
        printf("arg (");
        printProofTerm(node->args[0]->args.pterm);
        printf(")\n");
        break;
    }
    case SCOPE:
    {
        printf(":rule SCOPE\n");
        printf("premise(");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\narg(");
        for (int i = 0; i < node->arg_num; i++)
        {
            int num = node->args[i]->args.number;
            printf("assume:@p%d  ", num);
            printProofTerm(data->node_table[num]->concl);
            printf(" ");
        }
        printf(")\n");
        break;
    }
    case SET_VAR:
    {
        printf(":rule SET_VAR\n");
        printf("premise()\n arg(");
        printProofTerm(node->args[0]->args.pterm);
        printf(")\n");
        break;
    }
    case SET_PROP_IFF:
    {
        printf(":rule SET_PROP_IFF\n");
        printf("premise()\n arg(");
        printProofTerm(node->args[0]->args.pterm);
        printf(")\n");
        break;
    }
    case SET_PROP:
    {
        printf(":rule SET_PROP\n");
        printf("premise()\n arg(");
        printProofTerm(node->args[0]->args.pterm);
        printf(")\n");
        break;
    }
    case SUB_VAR:
    {
        printf(":rule SUB_VAR\n");
        printf("premise(");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\narg()\n");
        break;
    }
    case SUB_PROP:
    {
        printf(":rule SUB_PROP\n");
        printf("premise(");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\narg()\n");
        break;
    }
    case SUB_PROP_IFF:
    {
        printf(":rule SUB_PROP_IFF\n");
        printf("premise(");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\narg()\n");
        break;
    }
    case CNF_TRANS:
    {
        printf(":rule CNF_TRANS\n");
        printf("premise(");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\narg()\n");
        break;
    }
    case RESOLUTION:
    {
        printf(":rule RESOLUTION\n");
        printf("premise(");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(" , ");
        printProofTerm(data->node_table[node->premise_list[1]]->concl);
        printf(")\narg( %d )\n", node->args[0]->args.number);
        break;
    }
    case AND_ELIM:
    {
        printf(":rule AND_ELIM\n");
        printf("premise(");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\narg( %d )\n", node->args[0]->args.number);
        break;
    }
    case NOT_AND:
    {
        printf(":rule NOT_AND\n");
        printf("premise(");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\narg()\n");
        break;
    }
    case NOT_ELIM:{
        printf(":rule NOT_ELIM\n");
        printf("premise(");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\narg()\n");
        break;
    }
    case EQUALITY_RESOLUTION:
    {
        printf(":rule EQUALITY_RESOLUTION\n");
        printf("premise (");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(" , ");
        printProofTerm(data->node_table[node->premise_list[1]]->concl);
        printf(")\n arg ()\n");
        break;
    }
    case FUNC_REWRITE:
    {
        printf(":rule FUNC_REWRITE\n");
        printf("premise (");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(" , ");
        printProofTerm(data->node_table[node->premise_list[1]]->concl);
        printf(")\n arg ()\n");
        break;
    }
    case ARITH_FME:
    case ARITH_EQ_ELIM:
    {
        if (node->rule == ARITH_FME)
            printf(":rule ARITH_FME\n");
        else
            printf(":rule ARITH_EQ_ELIM\n");
        printf("premise (");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(" , ");
        printProofTerm(data->node_table[node->premise_list[1]]->concl);
        printf(")\n arg (");
        printf("x%d", node->args[0]->args.number);
        printf(")\n");
        break;
    }
    case ARITH_EQ_INTRO:
    {
        printf(":rule ARITH_EQ_INTRO\n");
        printf("premise (");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(" , ");
        printProofTerm(data->node_table[node->premise_list[1]]->concl);
        printf(")\n arg ( )\n");
        break;
    }
    case ARITH_FALSE:
    {
        printf("false :rule ARITH_FALSE\n");
        printf("premise (");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\n");
        printf("arg()\n");
        break;
    }
    case ARITH_NOT_ELIM:
    {
        printf(":rule ARITH_NOT_ELIM\n");
        printf("premise (");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\n");
        printf("arg()\n");
        break;
    }
    case ARITH_TRANS:
    {
        printf(":rule ARITH_TRANS\n");
        printf("premise (");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\n");
        printf("arg()\n");
        break;
    }
    case CONG:
    {
        printf(":rule CONG\n");
        printf("premise (");
        for (int i = 0; i < node->premise_num; i++)
        {
            printProofTerm(data->node_table[node->premise_list[i]]->concl);
            if (i != node->premise_num - 1)
                printf(" , ");
        }
        printf(")\n arg (\"%s\")\n", node->args[0]->args.func_name);
        break;
    }
    case TRANS:
    {
        printf(":rule TRANS\n");
        printf("premise (");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(" , ");
        printProofTerm(data->node_table[node->premise_list[1]]->concl);
        printf(")\n arg ()\n");
        break;
    }
    case REFL:
    {
        printf(":rule REFL\n");
        printf("premise ()\n");
        printf("arg()\n");
        break;
    }
    case SYMM:
    {
        printf(":rule SYMM\n");
        printf("premise (");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\n");
        printf("arg()\n");
        break;
    }
    case LIA_TRANS:
    {
        printf(":rule LIA_TRANS\n");
        printf("premise (");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(")\n");
        printf("arg()\n");
        break;
    }
    case UF_CONTRA_FALSE:
    {
        printf("false :rule UF_CONTRA_FALSE\n");
        printf("premise (");
        printProofTerm(data->node_table[node->premise_list[0]]->concl);
        printf(" , ");
        printProofTerm(data->node_table[node->premise_list[1]]->concl);
        printf(")\n");
        printf("arg()\n");
        break;
    }
    default:
        break;
    }
    printf("concl: (");
    printProofTerm(node->concl);
    printf(")\n");
}

int ProofTerm2Num(ProofTerm *t, Hash_Table *table1, Hash_Table *table2)
{
    char *s = ProofTerm2str(t);
    int *hval = NULL;
    if (table1 != NULL)
        hval = get_value_from_hstable(table1, s, strlen(s));
    if (hval == NULL && table2 != NULL)
        hval = get_value_from_hstable(table2, s, strlen(s));
    if (hval == NULL)
        return -1;
    else
        return *hval;
}

ProofTerm* newVarTerm(int v)
{
    ProofTerm *concl = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(concl, 0, sizeof(ProofTerm));
    concl->type = VAR;
    concl->arg_num = 0;
    concl->func_name.node_number = v;
    return concl;
}

ProofTerm *newPropVarTerm(int v)
{
    ProofTerm *concl = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(concl, 0, sizeof(ProofTerm));
    concl->type = PROP_VAR;
    concl->arg_num = 0;
    concl->func_name.node_number = v;
    return concl;
}

ProofTerm *newEqProofTerm(int a, int b)
{
    ProofTerm *concl = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(concl, 0, sizeof(ProofTerm));
    concl->type = FUNC_EQ;
    concl->arg_num = 2;
    concl->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * 2);
    concl->args[0] = newVarTerm(a);
    concl->args[1] = newVarTerm(b);
    return concl;
}

// res = t1 op t2 / res = not t1
ProofTerm *newPropTerm(ProofTerm *t1, ProofTerm *t2, TermType op)
{
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->type = op;
    if (op == FUNC_NOT)
    {
        res->arg_num = 1;
        res->args = (ProofTerm **)malloc(sizeof(ProofTerm *));
        res->args[0] = t1;
    }
    else
    {
        res->arg_num = 2;
        res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * 2);
        res->args[0] = t1;
        res->args[1] = t2;
    }
    return res;
}

// p > 0 返回 p , p < 0 返回 Not p
ProofTerm *newNotProp(int p)
{
    ProofTerm *p1 = NULL;
    if (p > 0)
        return newPropVarTerm(p);
    else if (p < 0)
        p1 = newPropVarTerm(-p);
    else
        return NULL;
    return newPropTerm(p1, NULL, FUNC_NOT);
}

// res = p1 \/ p2 \/ p3 , 负数表示NOT p， num表示clause中literal的个数，取值为2或3,小于3时p3设置为0
ProofTerm *newOrProp(int p1, int p2, int p3, int num)
{
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->type = FUNC_OR;
    res->arg_num = num;
    res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * num);
    res->args[0] = newNotProp(p1);
    res->args[1] = newNotProp(p2);
    if (num == 3)
        res->args[2] = newNotProp(p3);
    return res;
}

// res = t1 /\ t2 /\ t3 /\ t4  num至少为2，只多为4
ProofTerm *newAndProp(ProofTerm *t1, ProofTerm *t2, ProofTerm *t3, ProofTerm *t4, int num)
{
    ProofTerm *res = (ProofTerm *)malloc(sizeof(ProofTerm));
    memset(res, 0, sizeof(ProofTerm));
    res->type = FUNC_AND;
    res->arg_num = num;
    res->args = (ProofTerm **)malloc(sizeof(ProofTerm *) * num);
    res->args[0] = t1;
    res->args[1] = t2;
    if (num > 2)
        res->args[2] = t3;
    if (num > 3)
        res->args[3] = t4;
    return res;
}

ProofTerm *newEqProofTerm2(ProofTerm *t1, ProofTerm *t2)
{
    ProofTerm *concl = (ProofTerm *)malloc(sizeof(ProofTerm));
    concl->type = FUNC_EQ;
    concl->arg_num = 2;
    concl->args = (ProofTerm **)malloc(sizeof(ProofTerm *)*2);
    concl->args[0] = t1;
    concl->args[1] = t2;
    return concl;
}

ProofNode* newDeclareNode(int num, char* s){
    if(num == 0){
        //代表是函数的声明，只有一个参数，是函数名
        ArgTerm** args = (ArgTerm**)malloc(sizeof(ArgTerm*));
        args[0] = (ArgTerm*)malloc(sizeof(ArgTerm));
        args[0]->type = N_FUNC;
        args[0]->args.func_name = (char*)malloc(sizeof(char)*(strlen(s)+1));
        strcpy(args[0]->args.func_name, s);
        ProofNode* node = (ProofNode*)malloc(sizeof(ProofNode));
        memset(node, 0, sizeof(ProofNode));
        node->rule = DECLARE;
        node->arg_num = 1;
        node->args = args;
        node->concl = NULL;
        node->node_number = 0;
        node->premise_num = 0;
        node->premise_list = NULL;
        return node;
    }
    ArgTerm** args = (ArgTerm**)malloc(sizeof(ArgTerm*)*2);
    args[0] = (ArgTerm*)malloc(sizeof(ArgTerm));
    args[1] = (ArgTerm*)malloc(sizeof(ArgTerm));
    memset(args[0], 0, sizeof(ArgTerm));
    memset(args[1], 0, sizeof(ArgTerm));
    args[0]->type = NUM;
    args[0]->args.number = num;
    args[1]->type = N_FUNC;
    args[1]->args.func_name = (char*)malloc(sizeof(char)*(strlen(s)+1));
    strcpy(args[1]->args.func_name, s);
    ProofNode* node = (ProofNode*)malloc(sizeof(ProofNode));
    memset(node, 0, sizeof(ProofNode));
    node->rule = DECLARE;
    node->arg_num = 2;
    node->args = args;
    node->concl = NULL;
    node->node_number = 0;
    node->premise_num = 0;
    node->premise_list = NULL;
    return node;
}

void updata_DeclareData(ProofNode* node, ProofData* pdata){
    if (pdata->declare_num > pdata->declare_max_num)
    {
        // 扩容declare_table
        pdata->declare_max_num *= 2;
        ProofNode **res = (ProofNode **)realloc(pdata->declare_table, (pdata->declare_max_num + 1) * sizeof(ProofNode *));
        if (res == NULL)
        {
            printf("memory is not enough\n");
            exit(-1);
        }
        pdata->declare_table = res;
    }
    pdata->declare_table[pdata->declare_num] = node;
}

void freeSmtProof(SMT_PROOF* proof){
    if (proof == NULL) return;
    for(int i = 1; i <= proof->proof_num; i++){
        freeProofNode(proof->proof_table[i]);
    }
    for(int i = 1; i <= proof->declare_num; i++) {
        freeProofNode(proof->declare_table[i]);
    }
    free(proof->proof_table);
    free(proof->declare_table);
    free(proof);
}

void freeProofData(ProofData* pdata){
    for(int i = 1; i <= pdata->cur_num; i++){
        freeProofNode(pdata->node_table[i]);
    }
    for(int i = 1; i <= pdata->declare_num; i++) {
        freeProofNode(pdata->declare_table[i]);
    }
    hash_table_delete(pdata->global_table);
    hash_table_delete(pdata->theory_global_table);
    hash_table_delete(pdata->local_table);
    free(pdata->node_table);
    free(pdata->declare_table);
    free(pdata);
}